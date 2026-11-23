use std::ffi::{CStr, CString};
use std::fs::{File, OpenOptions};
use std::io::{self, Read};
use std::mem::MaybeUninit;
use std::os::fd::{AsRawFd, FromRawFd, IntoRawFd, RawFd};
use std::os::unix::fs::OpenOptionsExt;
use std::path::Path;
use std::ptr::NonNull;

pub struct Site {
    // Four words per file: key offset and length, then body offset and length.
    entries: Vec<u32>,
    blob: Vec<u8>,
}

impl Site {
    pub fn load(root: &Path) -> io::Result<Self> {
        let root = OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_DIRECTORY)
            .open(root)?;
        let mut site = Self {
            entries: Vec::new(),
            blob: Vec::new(),
        };
        site.walk(root, &mut Vec::new(), 0)?;
        Ok(site)
    }

    pub fn as_parts(&self) -> (&[u32], &[u8]) {
        (&self.entries, &self.blob)
    }

    fn walk(&mut self, fd: File, key: &mut Vec<u8>, depth: usize) -> io::Result<()> {
        if depth > 16 {
            return Ok(());
        }
        let mut dir = Directory::new(fd)?;
        while let Some(name) = dir.next()? {
            let segment = name.as_bytes();
            let prefix_len = key.len();
            if segment.is_empty()
                || segment[0] == b'.'
                || !segment
                    .iter()
                    .all(|b| b.is_ascii_alphanumeric() || b"._~-".contains(b))
                || prefix_len + segment.len() >= 1024
            {
                continue;
            }
            let kind = dir.kind(&name);
            let directory = match kind {
                Some(libc::S_IFDIR) => true,
                Some(libc::S_IFREG) => false,
                _ => continue,
            };
            let Ok(file) = dir.open(&name, directory) else {
                continue;
            };
            key.extend_from_slice(segment);
            if directory {
                key.push(b'/');
                self.walk(file, key, depth + 1)?;
            } else {
                // Check the opened descriptor as the entry could change after fstatat.
                let metadata = file.metadata()?;
                if metadata.is_file() {
                    self.add(file, key, metadata.len())?;
                }
            }
            key.truncate(prefix_len);
        }
        Ok(())
    }

    fn add(&mut self, mut file: File, key: &[u8], size: u64) -> io::Result<()> {
        let start = self.blob.len();
        let body = start + key.len();
        if body as u64 + size > 0x7fff_ffff || self.entries.len() > u32::MAX as usize - 4 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "site exceeds snapshot limit",
            ));
        }
        let size = size as usize;
        self.blob
            .try_reserve(key.len() + size)
            .map_err(io::Error::other)?;
        self.entries.try_reserve(4).map_err(io::Error::other)?;
        self.blob.extend_from_slice(key);
        self.blob.resize(body + size, 0);
        file.read_exact(&mut self.blob[body..])?;
        self.entries
            .extend([start as u32, key.len() as u32, body as u32, size as u32]);
        Ok(())
    }
}

struct Directory(NonNull<libc::DIR>);

impl Directory {
    fn new(file: File) -> io::Result<Self> {
        // fdopendir takes ownership of the descriptor on success only.
        let dir = NonNull::new(unsafe { libc::fdopendir(file.as_raw_fd()) })
            .ok_or_else(io::Error::last_os_error)?;
        let _ = file.into_raw_fd();
        Ok(Self(dir))
    }

    fn fd(&self) -> RawFd {
        // The DIR remains live for this borrow.
        unsafe { libc::dirfd(self.0.as_ptr()) }
    }

    fn next(&mut self) -> io::Result<Option<CString>> {
        // A null return with errno zero denotes EOF. Copy d_name before the next call.
        unsafe {
            *libc::__errno_location() = 0;
            let entry = libc::readdir(self.0.as_ptr());
            if entry.is_null() {
                if *libc::__errno_location() == 0 {
                    return Ok(None);
                }
                return Err(io::Error::last_os_error());
            }
            Ok(Some(
                CStr::from_ptr(std::ptr::addr_of!((*entry).d_name).cast()).to_owned(),
            ))
        }
    }

    fn kind(&self, name: &CStr) -> Option<libc::mode_t> {
        let mut stat = MaybeUninit::<libc::stat>::uninit();
        // fstatat initializes stat on success and reads the terminated name.
        unsafe {
            if libc::fstatat(
                self.fd(),
                name.as_ptr(),
                stat.as_mut_ptr(),
                libc::AT_SYMLINK_NOFOLLOW,
            ) != 0
            {
                return None;
            }
            Some(stat.assume_init().st_mode & libc::S_IFMT)
        }
    }

    fn open(&self, name: &CStr, directory: bool) -> io::Result<File> {
        let mut flags = libc::O_RDONLY | libc::O_NOFOLLOW | libc::O_CLOEXEC | libc::O_NONBLOCK;
        if directory {
            flags |= libc::O_DIRECTORY;
        }
        // openat creates a new descriptor whose ownership transfers to File.
        let fd = unsafe { libc::openat(self.fd(), name.as_ptr(), flags) };
        if fd < 0 {
            return Err(io::Error::last_os_error());
        }
        Ok(unsafe { File::from_raw_fd(fd) })
    }
}

impl Drop for Directory {
    fn drop(&mut self) {
        // closedir releases the stream and the descriptor it owns.
        unsafe { libc::closedir(self.0.as_ptr()) };
    }
}
