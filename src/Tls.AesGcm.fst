module Tls.AesGcm

(* The pinned x86-64 Vale GCM wrappers specify the two little-endian
   operations below. TLS supplies a 96-bit nonce, a five-byte record header
   as additional data, and a combined ciphertext and 16-byte tag. *)
open Vale.AES.AES_s
open Vale.AES.GCTR_s
open Vale.AES.GCM_s
open Vale.Def.Types_s
open Vale.Def.Words_s
open Vale.Def.Words.Seq_s
module S = FStar.Seq

(* These length lemmas follow the pinned Vale.AES.GCTR proof and depend
   only on the specification modules. *)
#push-options "--max_ifuel 1"
noextract let rec counter_blocks_length (counter:quad32) (plain:gctr_plain_internal_LE)
    (alg:algorithm) (k:aes_key_LE alg) (i:int)
    : Lemma (ensures S.length (gctr_encrypt_recursive counter plain alg k i) = S.length plain)
      (decreases (S.length plain)) =
  if S.length plain = 0 then ()
  else counter_blocks_length counter (S.tail plain) alg k (i + 1)
#pop-options

#push-options "--z3rlimit 40"
noextract let counter_bytes_length (counter:quad32) (plain:gctr_plain_LE)
    (alg:algorithm) (k:aes_key_LE alg)
    : Lemma (S.length (gctr_encrypt_LE counter plain alg k) = S.length plain)
      [SMTPat (S.length (gctr_encrypt_LE counter plain alg k))] =
  reveal_opaque (`%le_bytes_to_seq_quad32) le_bytes_to_seq_quad32;
  gctr_encrypt_LE_reveal ();
  let tail_len = S.length plain % 16 in
  let full_blocks = S.slice plain 0 (S.length plain - tail_len) in
  if tail_len = 0 then
    counter_blocks_length counter (le_bytes_to_seq_quad32 plain) alg k 0
  else
    counter_blocks_length counter (le_bytes_to_seq_quad32 full_blocks) alg k 0

noextract let encrypt_lengths (k:aes_key AES_128) (iv:supported_iv_LE)
    (plain:gcm_plain_LE) (aad:gcm_auth_LE)
    : Lemma (let c, tag = gcm_encrypt_LE AES_128 k iv plain aad in
             S.length c = S.length plain /\ S.length tag = 16) =
  gcm_encrypt_LE_reveal ();
  let key_words = seq_nat8_to_seq_nat32_LE k in
  let hash_key = aes_encrypt_LE AES_128 key_words (Mkfour 0 0 0 0) in
  let initial_counter = compute_iv_BE hash_key iv in
  counter_bytes_length (inc32 initial_counter 1) plain AES_128 key_words;
  let _, tag = gcm_encrypt_LE AES_128 k iv plain aad in
  assert (S.length tag = 16)

noextract let decrypt_length (k:aes_key AES_128) (iv:supported_iv_LE)
    (cipher:gcm_plain_LE) (aad:gcm_auth_LE) (tag:S.seq nat8)
    : Lemma (let p, _ = gcm_decrypt_LE AES_128 k iv cipher aad tag in
             S.length p = S.length cipher) =
  gcm_decrypt_LE_reveal ();
  let key_words = seq_nat8_to_seq_nat32_LE k in
  let hash_key = aes_encrypt_LE AES_128 key_words (Mkfour 0 0 0 0) in
  let initial_counter = compute_iv_BE hash_key iv in
  counter_bytes_length (inc32 initial_counter 1) cipher AES_128 key_words
#pop-options

let encrypt k iv aad plain =
  let k = seq_uint8_to_seq_nat8 k in
  let iv = seq_uint8_to_seq_nat8 iv in
  let aad = seq_uint8_to_seq_nat8 aad in
  let plain = seq_uint8_to_seq_nat8 plain in
  let cipher, tag = gcm_encrypt_LE AES_128 k iv plain aad in
  encrypt_lengths k iv plain aad;
  S.append (seq_nat8_to_seq_uint8 cipher) (seq_nat8_to_seq_uint8 tag)

let decrypt k iv aad c =
  let k = seq_uint8_to_seq_nat8 k in
  let iv = seq_uint8_to_seq_nat8 iv in
  let aad = seq_uint8_to_seq_nat8 aad in
  let pos = S.length c - 16 in
  let cipher = seq_uint8_to_seq_nat8 (S.slice c 0 pos) in
  let tag = seq_uint8_to_seq_nat8 (S.slice c pos (S.length c)) in
  let plain, authenticated = gcm_decrypt_LE AES_128 k iv cipher aad tag in
  decrypt_length k iv cipher aad tag;
  if authenticated then Some (seq_nat8_to_seq_uint8 plain) else None
