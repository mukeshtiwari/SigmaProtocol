From Stdlib Require Import Extraction 
ExtrOcamlBasic ExtrOcamlNativeString
ExtrOcamlZBigInt ExtrOcamlNatBigInt.
From Examples Require Import BeleniosIns Ed25519Ins.
Set Extraction Output Directory ".". 
Separate Extraction BeleniosIns Ed25519Ins.
