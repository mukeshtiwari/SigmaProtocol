From Stdlib Require Import Extraction 
ExtrOcamlBasic ExtrOcamlNativeString
ExtrOcamlZBigInt ExtrOcamlNatBigInt.
From Compiler Require Import CompilerIns.
Extraction Blacklist String List Nat Ascii Byte Decimal.
Set Extraction Output Directory ".". 
Separate Extraction CompilerIns.
