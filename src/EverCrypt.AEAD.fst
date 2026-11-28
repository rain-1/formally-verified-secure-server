module EverCrypt.AEAD
(* TRUSTED INTERFACE: binding to EverCrypt_AEAD_{en,de}crypt_expand_aes128_gcm (HACL*/Vale, x86-64 AES-NI).
   One-shot: expands the key on every call, so no heap state is needed.
   Return value: 0 = success, 3 = authentication failure, others = unsupported/invalid. *)
open FStar.HyperStack.ST
module B = LowStar.Buffer
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module S = FStar.Seq
module Spec = Tls.Spec

(* The runtime check after AutoConfig2 initialization. The linked build and
   CPU feature flags stay fixed for the modeled connection. *)
noextract assume val aes128gcm_available : unit -> Tot bool

assume val encrypt_expand_aes128_gcm :
    k:B.buffer U8.t -> iv:B.buffer U8.t -> iv_len:U32.t -> ad:B.buffer U8.t -> ad_len:U32.t ->
    plain:B.buffer U8.t -> plain_len:U32.t -> cipher:B.buffer U8.t -> tag:B.buffer U8.t
  -> Stack U8.t
     (requires fun h -> B.live h k /\ B.live h iv /\ B.live h ad /\ B.live h plain /\ B.live h cipher /\ B.live h tag /\
        B.length k = 16 /\ B.length iv = 12 /\ U32.v iv_len = 12 /\ B.length ad = U32.v ad_len /\
        B.length ad = 5 /\ B.length plain <= 16640 /\
        B.length plain = U32.v plain_len /\ B.length cipher = U32.v plain_len /\ B.length tag = 16 /\
        B.disjoint cipher plain /\ B.disjoint cipher tag /\ B.disjoint cipher ad /\ B.disjoint cipher k /\
        B.disjoint cipher iv /\ B.disjoint tag plain /\ B.disjoint tag ad /\ B.disjoint tag k /\ B.disjoint tag iv)
     (ensures fun h0 r h1 -> B.modifies (B.loc_union (B.loc_buffer cipher) (B.loc_buffer tag)) h0 h1 /\
        r == (if aes128gcm_available () then 0uy else 1uy) /\
        (r == 0uy ==> S.append (B.as_seq h1 cipher) (B.as_seq h1 tag) ==
          Spec.record_encrypt Spec.Aes128Gcm (B.as_seq h0 k) (B.as_seq h0 iv) (B.as_seq h0 ad) (B.as_seq h0 plain)))

assume val decrypt_expand_aes128_gcm :
    k:B.buffer U8.t -> iv:B.buffer U8.t -> iv_len:U32.t -> ad:B.buffer U8.t -> ad_len:U32.t ->
    cipher:B.buffer U8.t -> cipher_len:U32.t -> tag:B.buffer U8.t -> dst:B.buffer U8.t
  -> Stack U8.t
     (requires fun h -> B.live h k /\ B.live h iv /\ B.live h ad /\ B.live h cipher /\ B.live h tag /\ B.live h dst /\
        B.length k = 16 /\ B.length iv = 12 /\ U32.v iv_len = 12 /\ B.length ad = U32.v ad_len /\
        B.length ad = 5 /\ B.length cipher + 16 <= 16640 /\
        B.length cipher = U32.v cipher_len /\ B.length tag = 16 /\ B.length dst = U32.v cipher_len /\
        B.disjoint dst cipher /\ B.disjoint dst tag /\ B.disjoint dst ad /\ B.disjoint dst k /\ B.disjoint dst iv)
     (ensures fun h0 r h1 -> B.modifies (B.loc_buffer dst) h0 h1 /\
        (if aes128gcm_available () then r == 0uy \/ r == 3uy else r == 1uy) /\
        (let plain = Spec.record_decrypt Spec.Aes128Gcm (B.as_seq h0 k) (B.as_seq h0 iv) (B.as_seq h0 ad)
            (S.append (B.as_seq h0 cipher) (B.as_seq h0 tag)) in
         (r == 0uy ==> plain == Some (B.as_seq h1 dst)) /\
         (r == 3uy ==> plain == None)))
