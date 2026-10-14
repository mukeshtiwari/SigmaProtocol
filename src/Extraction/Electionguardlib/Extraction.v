From Stdlib Require Import Extraction 
ExtrOcamlBasic ExtrOcamlNativeString
ExtrOcamlZBigInt ExtrOcamlNatBigInt.
From Examples Require Import ElectionGuardIns.
Set Extraction Output Directory ".". 
Separate Extraction ElectionGuardIns.
