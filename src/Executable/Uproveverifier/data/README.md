# U-Prove test vectors

The twelve `testvectors_EC_*_doc.txt` files are the official test vectors of
the U-Prove Cryptographic Specification V1.1 Revision 3 (the current
Revision 5, March 2023, changes no algorithm and cites these same vectors), generated with
Microsoft's U-Prove C# SDK (`UProveUnitTest/TestVectorData`, commit
b61315e, Apache License 2.0) for the elliptic-curve construction at P-256
with SHA-256 (recommended parameters OID 1.3.6.1.4.1.311.75.1.2.1). Each
file is a complete protocol run: Issuer parameters (`y0`, `g0`, `e_i`, `S`),
attributes `A1..A5`, issuance (`sigma*`, `alpha`, `beta*`, the token `h`,
`sigmaZPrime`, `sigmaCPrime`, `sigmaRPrime`) and a presentation proof
(`a`, `r0`, `r_i`, and in the non-`lite` files the pseudonym `ap`, `Ps`
and the commitments `tildeC_i`, `tildeA_i`, `tildeR_i`). The files differ in
the disclosed set (`D0`, `D2`, `D5`: no, two or all five attributes
disclosed) and in Device protection (`Device_*`, with `xd`, `hd`, `rd`).
`testvectors_hashing.txt` holds the hash-formatting vectors of spec
section 2.2.

The `ie_*`, `r_*` and `sm_*` values (identity-escrow, revocation and
set-membership extensions) are not used by the verifier.

Verification: `dune exec src/Executable/Uproveverifier/main.exe -- --tamper`.
