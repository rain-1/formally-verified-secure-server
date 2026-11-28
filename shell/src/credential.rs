const SEQUENCE: u8 = 0x30;
const INTEGER: u8 = 0x02;
const BIT_STRING: u8 = 0x03;
const OBJECT_IDENTIFIER: u8 = 0x06;
const EXPLICIT_VERSION: u8 = 0xa0;

// id-ecPublicKey (1.2.840.10045.2.1) and secp256r1 (1.2.840.10045.3.1.7).
const EC_PUBLIC_KEY: &[u8] = &[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01];
const P256: &[u8] = &[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07];

// Read one expected DER TLV. At MAX_CHAIN, a canonical length takes at most
// two content-length bytes. Return the value and advance within its parent.
fn take_der<'a>(input: &mut &'a [u8], tag: u8) -> Option<&'a [u8]> {
    let (&actual, input_after_tag) = input.split_first()?;
    if actual != tag {
        return None;
    }
    let (len, rest) = match input_after_tag {
        [short @ 0..=0x7f, rest @ ..] => (usize::from(*short), rest),
        [0x81, long @ 0x80..=0xff, rest @ ..] => (usize::from(*long), rest),
        [0x82, hi @ 1..=0xff, lo, rest @ ..] => (usize::from(u16::from_be_bytes([*hi, *lo])), rest),
        _ => return None,
    };
    let value = rest.get(..len)?;
    *input = rest.get(len..)?;
    Some(value)
}

pub(crate) fn leaf_p256_point(chain: &[u8]) -> Option<&[u8]> {
    // The first TLS CertificateEntry contains the leaf. Its u24 length
    // bounds the DER certificate independently of extensions and other entries.
    let [hi, mid, lo, entries @ ..] = chain else {
        return None;
    };
    let len = u32::from_be_bytes([0, *hi, *mid, *lo]) as usize;
    let mut leaf = entries.get(..len)?;
    let [ext_hi, ext_lo, after_ext_len @ ..] = entries.get(len..)? else {
        return None;
    };
    after_ext_len.get(..usize::from(u16::from_be_bytes([*ext_hi, *ext_lo])))?;

    let mut certificate = take_der(&mut leaf, SEQUENCE)?;
    let mut tbs = take_der(&mut certificate, SEQUENCE)?;
    take_der(&mut certificate, SEQUENCE)?; // signatureAlgorithm
    take_der(&mut certificate, BIT_STRING)?; // signatureValue
    if !leaf.is_empty() || !certificate.is_empty() {
        return None;
    }

    // RFC 5280 §4.1. Locate SubjectPublicKeyInfo by its position in
    // TBSCertificate so bytes in an extension or another field cannot match.
    if tbs.first() == Some(&EXPLICIT_VERSION) {
        let mut version = take_der(&mut tbs, EXPLICIT_VERSION)?;
        take_der(&mut version, INTEGER)?;
        if !version.is_empty() {
            return None;
        }
    }
    take_der(&mut tbs, INTEGER)?; // serialNumber
    take_der(&mut tbs, SEQUENCE)?; // signature
    take_der(&mut tbs, SEQUENCE)?; // issuer
    take_der(&mut tbs, SEQUENCE)?; // validity
    take_der(&mut tbs, SEQUENCE)?; // subject
    let mut spki = take_der(&mut tbs, SEQUENCE)?;

    // RFC 5480 §§2.1–2.2. Require the algorithm, named curve and an
    // octet-aligned ECPoint in the SPKI BIT STRING.
    let mut algorithm = take_der(&mut spki, SEQUENCE)?;
    if take_der(&mut algorithm, OBJECT_IDENTIFIER)? != EC_PUBLIC_KEY
        || take_der(&mut algorithm, OBJECT_IDENTIFIER)? != P256
        || !algorithm.is_empty()
    {
        return None;
    }
    let bits = take_der(&mut spki, BIT_STRING)?;
    let (&0, point) = bits.split_first()? else {
        return None;
    };
    if !spki.is_empty() || !matches!(point.len(), 33 | 65) {
        return None;
    }
    Some(point)
}
