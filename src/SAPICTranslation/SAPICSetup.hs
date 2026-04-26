module SAPICSetup (sapicTheoryHeader, sapicTheoryFooter) where

-- | SAPIC+ theory preamble.
-- We declare the ProVerif-style helper symbols that the IR carries through
-- (vscrypt, vsign, fst, snd, pubk, ...) as plain function symbols. This is
-- enough to make the file parse; full equational semantics is future work.
sapicTheoryHeader :: String -> String
sapicTheoryHeader name = unlines
    [ "theory " ++ name
    , "begin"
    , ""
    , "// Tamarin builtins cover symmetric encryption and DH."
    , "// scrypt/dscrypt -> senc/sdec; exp/g -> ^/'g'."
    , "// Asymmetric encryption stays ProVerif-flavored (see equations)."
    , "builtins: symmetric-encryption, diffie-hellman"
    , ""
    , "// ProVerif-style helpers (asymmetric encryption / signatures /"
    , "// pattern checks). Names that collide with Tamarin builtins are"
    , "// prefixed with pv_."
    , "functions:"
    , "  vscrypt/2, vcrypt/2, vsign/2, vinv/1, vpair/1,"
    , "  pv_sign/2, open/2,"
    , "  pv_pk/1, pv_inv/1 [private], pubk/1,"
    , "  crypt/2, dcrypt/2,"
    , "  pv_fst/1, pv_snd/1,"
    , "  pv_kdf/1, invkdf/1, skdf/1,"
    , "  pubkey2bitstring/1, agent2bitstring/1, skey2bitstring/1, privkey2bitstring/1,"
    , "  sk/2 [private],"
    , "  pv_true/0, api_call_baton/0"
    , ""
    , "// Equational theory faithful to the ProVerif protocol setup:"
    , "//   pubk(inv(k)) = k                       -- private key determines public key"
    , "//   dcrypt(crypt(m, k), inv(k)) = m        -- asymmetric decryption"
    , "//   open(sign(m, inv(k)), k) = m           -- recover signed message"
    , "// Plus positive branches of the ProVerif validity-check destructors"
    , "// (vsign/vcrypt/vscrypt/vinv/vpair); the negative defaults"
    , "// (vsign(_,_) = false otherwise) are not expressible in Tamarin's"
    , "// equational fragment. Without the positive branches, every"
    , "// validity check would block, leaving the protocol dead in"
    , "// Tamarin's semantics."
    , "equations:"
    , "  pubk(pv_inv(x)) = x,"
    , "  dcrypt(crypt(x, k), pv_inv(k)) = x,"
    , "  open(pv_sign(x, pv_inv(k)), k) = x,"
    , "  vsign(pv_sign(x, pv_inv(k)), k) = pv_true,"
    , "  vcrypt(crypt(x, k), pv_inv(k)) = pv_true,"
    , "  vscrypt(senc(x, k), k) = pv_true,"
    , "  vinv(pv_inv(x)) = pv_true,"
    , "  vpair(<x, y>) = pv_true"
    , ""
    ]

sapicTheoryFooter :: String
sapicTheoryFooter = "end\n"
