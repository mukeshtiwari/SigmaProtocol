From Stdlib Require Import Extraction 
ExtrOcamlBasic ExtrOcamlNativeString
ExtrOcamlZBigInt ExtrOcamlNatBigInt.
From Examples Require Import BayerGrothE2EIns SwissPostZkpE2EIns.
Set Extraction Output Directory ".". 
Separate Extraction BayerGrothE2EIns SwissPostZkpE2EIns.
