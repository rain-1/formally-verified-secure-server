use std::path::Path;

fn main() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../_build/native");
    println!(
        "cargo:rerun-if-changed={}",
        dir.join("libsws_core.a").display()
    );
    println!("cargo:rustc-link-search=native={}", dir.display());
    println!("cargo:rustc-link-lib=static=sws_core");
}
