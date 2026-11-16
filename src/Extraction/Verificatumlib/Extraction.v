From Stdlib Require Import Extraction 
ExtrOcamlBasic ExtrOcamlNativeString
ExtrOcamlZBigInt ExtrOcamlNatBigInt.
From Examples Require Import VerificatumIns HeliosTallyIns.
Set Extraction Output Directory ".". 
Separate Extraction VerificatumIns HeliosTallyIns.
