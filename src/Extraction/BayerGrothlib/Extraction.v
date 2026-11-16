From Stdlib Require Import Extraction 
ExtrOcamlBasic ExtrOcamlNativeString
ExtrOcamlZBigInt ExtrOcamlNatBigInt.
From Examples Require Import BayerGrothIns.
Set Extraction Output Directory ".". 
Separate Extraction BayerGrothIns.
