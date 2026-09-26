From Stdlib Require Import Extraction 
ExtrOcamlBasic ExtrOcamlNativeString
ExtrOcamlZBigInt ExtrOcamlNatBigInt.
From Examples Require Import Ed25519Ins.
Set Extraction Output Directory ".". 
Separate Extraction Ed25519Ins.
