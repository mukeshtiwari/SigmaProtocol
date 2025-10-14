# Dlog-zkp
Formalisation of Schnorr Protocol and other proofs (https://www.win.tue.nl/~berry/2WC13/LectureNotes.pdf)

Here is my plan to proceed:

1. I am going to write a concrete implementation of Group and Field 
    and their respective functions (addition, multiplication, division,
    etc), assuming the Schnorr group. (Finished)
2. Then I write a power function that interacts between Group and 
    Field and show that it respects the vector-space axioms. (Finished)
3. Now that we have all the concrete implementation, we can 
   demonstrate that they are efficient. (Finished)
4. Formalise others, e.g., Parallel, EQ, AND, OR sigma protocol (Finished)
5. Formalise some vote counting method where we can use our 
   sigma protocol library to demonstrate usability. 


The end goal is verify all the crypto primitives of [SwissPost](https://gitlab.com/swisspost-evoting/crypto-primitives/crypto-primitives/) in Coq.

Run `dune build` (ignore the warinings) in this directory to compile the project. It will compile the Rocq code and 
generate OCaml code from it [_CoqProject file](/_CoqProject). It takes a while (3 hours) because it verifies the primality and generator order in Rocq [SigmaInsHelios.v](/src/Examples/SigmaInsHelios.v) used in [Helios](https://github.com/benadida/js-voting-crypto/blob/master/test/elgamal-test.js#L14). `dune build  6554.20s user 15.53s system 57% cpu 3:08:53.70 total`. If you want to compile it quickly, comment out all the code in [SigmaInsHelios.v](/src/Examples/SigmaInsHelios.v), [primeP.v](/src/Examples/primeP.v), [primeQ.v](/src/Examples/primeQ.v), and [main.ml](/src/Executable/SigmaHelios/main.ml).
1. Run `dune exec _build/default/src/Executable/SigmaHelios/main.exe` to run the Helios example. You will output like this:
   ```OCaml
   (base) mukesh.tiwari@Mukeshs-MacBook-Pro-2 SigmaProtocol % dune exec _build/default/src/Executable/SigmaHelios/main.exe 
   p = 16328632084933010002384055033805457329601614771185955389739167309086214800406465799038583634953752941675645562182498120750264980492381375579367675648771293800310370964745767014243638518442553823973482995267304044326777047662957480269391322789378384619428596446446984694306187644767462460965622580087564339212631775817895958409016676398975671266179637898557687317076177218843233150695157881061257053019133078545928983562221396313169622475509818442661047018436264806901023966236718367204710755935899013750306107738002364137917426595737403871114187750804346564731250609196846638183903982387884578266136503697493474682071, q = 61329566248342901292543872769978950870633559608669337131139375508370458778917, g = 14887492224963187634282421537186040801304008017743492304481737382571933937568724473847106029915040150784031882206090286938661464458896494215273989547889201144857352611058572236578734319505128042602372864570426550855201448111746579871811249114781674309062693442442368697449970648232621880001709535143047913661432883287150003429802392229361583608686643243349727791976247247948618930423866180410558458272606627111270040091203073580238905303994472202930783207472394578498507764703191288249547659899997131166130259700604433891232298182348403175947450284433411265966789131024573629546048637848902243503970966798589660808533, h = 8712008288323819069611104926654842045723778356018808688755872544171633789079557392507192845307035988302951719349750357518969479793296048790766419242280955777101567726561115504822877896350494241763119864586638259866510244447154254643855542445517679072605644287956242816129459190724051385871892116314630571348662816132072056944378867349253890588904328270619665125727970737450057090996395788369855060669545401704125307852911854705899065930168341527640746489256475460926064718511758476372128677599075387923904232187958366871647449427908842504496667424640873836781685306450539101397934464789668056433260066933489061552308 
   proof = {annoucement = 7377738566459993093442909511731475429771184823730543650274913004475876318705236271824069250349634229650877205853671596166335931119180353663715324339060824632556683689033877367565959767475638146851144740698046340702599236874313618016935730601243813541487430306983172302534339925602234471064990001184910451013487009555894005407161628755282226490372845019326384591232540268127624384033369409066245330778189036413310771248286174503165463207251936264284593654807676571327607630344170165638458274468330015410637275582116631079969578086341799387607729293325308909317334852717811091342014895043807308300875837918815381362226,  challenge = 21192296258708538860065659937602565879522491974624428752185010965328412529808,  response = 26685548330706968310179871065796897612491865672257011470232304456681983178792, } 
   true%
   ```

2. Run `dune exec _build/default/src/Executable/Sigmacode/main.exe` to run the sigma protocol. You will see an output like this:
   ```OCaml
   (base) mukesh.tiwari@Mukeshs-MacBook-Pro-2 SigmaProtocol % dune exec _build/default/src/Executable/Sigmacode/main.exe
    p = 5927, q = 2963, g = 4, h = 64
    proof = {annoucement = 1644,  challenge = 1987,  response = 2269, }
    true%
    ```
3. Run `dune exec _build/default/src/Executable/AndSigmacode/main.exe` to run the AndSigma protocol. You will see an output like this:
   ```OCaml
   (base) mukesh.tiwari@Mukeshs-MacBook-Pro-2 SigmaProtocol % dune exec _build/default/src/Executable/AndSigmacode/main.exe
    p = 5927, q = 2963, g = 4, h1 = 64, h2 = 1024, h3 = 339
    proof = {annoucement = 2036, 2070, 3797,  challenge = 461,  response = 1709, 1298, 722, }
    true%
   ```
4. Run `dune exec _build/default/src/Executable/ParaSigmacode/main.exe` to run the Parallel Sigma protocol. You will see an output like this:
   ```OCaml
   (base) mukesh.tiwari@Mukeshs-MacBook-Pro-2 SigmaProtocol % dune exec _build/default/src/Executable/ParaSigmacode/main.exe
    p = 5927, q = 2963, g = 4, h = 64
    proof = {annoucement = 4823, 4334,  challenge = 2303, 2717,  response = 2634, 1787, }
    true%
   ```
5. Run `dune exec _build/default/src/Executable/Elgamalcode/main.exe` to run the Elgamal encryption functions. You will see an output like this: 
   ```OCaml
   (base) mukesh.tiwari@Mukeshs-MacBook-Pro-2 SigmaProtocol % dune exec _build/default/src/Executable/Elgamalcode/main.exe
   message ms1 = 964, 671, 491, 2074, 2463, 2805, 2937, 1892, 1466, 275
   encryption cs1 = (3805, 111), (2760, 2509), (3922, 3482), (2089, 5014), (1741, 3154), (5590, 5523), (467, 3231), (1014, 2342), (811, 4961), (1846, 4579)
   decryption ds1 = 964, 671, 491, 2074, 2463, 2805, 2937, 1892, 1466, 275
   rencryption cs2 = (813, 2489), (1928, 3368), (2613, 4572), (656, 2401), (3123, 4669), (2457, 1002), (5405, 200), (4538, 3859), (5604, 1199), (1771, 3421)
   decryption ds2 = 964, 671, 491, 2074, 2463, 2805, 2937, 1892, 1466, 275
   multiplication enc ballot cs3 = (5498, 3637), (4761, 4337), (403, 5709), (1247, 877), (2084, 3358), (1771, 4155), (5160, 157), (2180, 5030), (4762, 3458), (3489, 5625)
   decryption ds3 = 1928, 1342, 982, 1185, 1963, 2647, 2911, 821, 2932, 550%
   ```
6. Run `dune exec _build/default/src/Executable/OrSigmacode/main.exe` to run the OR Sigma protocol. You will see an output like this:
   ```OCaml 
   (base) mukesh.tiwari@Mukeshs-MacBook-Pro-2 SigmaProtocol % dune exec _build/default/src/Executable/OrSigmacode/main.exe
   p = 5927, q = 2963, g = 4, h_UU2081_  = 12, h_UU2082_  = 64, h_UU2083_  = 25, com = 3173, 1573, 1351,
   proof = {annoucement = 3173, 1573, 1351,  challenge = 1723, 1429, 2530, 727,  response = 455, 2825, 1712, }
   true%
   ```
7. Run `dune exec _build/default/src/Executable/EncProofcode/main.exe` to run the Encryption Proof Sigma protocol. You will see an output like this: 
   ```OCaml
   (base) mukesh.tiwari@Mukeshs-MacBook-Pro-2 SigmaProtocol % dune exec _build/default/src/Executable/EncProofcode/main.exe
   p = 5927, q = 2963, g = 12, h  = 25, m_UU2080_  = 28, m_UU2081_  = 134, m_UU2082_ = 38, cp = (3108, 450), com = (83, 5583), (4551, 5153), (72, 586)
   proof = {annoucement = (83, 5583), (3021, 5294), (3534, 677) challenge = 2026, 2515, 1078, 1396 response = 1448, 228, 2263}
   true%
   ```
8. Run `dune exec _build/default/src/Executable/EqSigmacode/main.exe` to run the EQ Sigma protocol. You will see an output like this: 
   ```OCaml
   (base) mukesh.tiwari@Mukeshs-MacBook-Pro-2 SigmaProtocol % dune exec _build/default/src/Executable/EqSigmacode/main.exe
   p = 5927, q = 2963, g_UU2081_ = 12, g_UU2082_ = 16, g_UU2083_ = 18, h_UU2081_ = 1728, h_UU2082_ = 4096, h_UU2083_ = 18, com = 4026, 2686, 5005
   proof = {annoucement = 4026, 2686, 5005 challenge = 2010 response = 596}
   true%
   ```
9. Run `dune exec _build/default/src/Executable/Approvalcode/main.exe` to run the Approval voting. You will see an output like [this](/src/Executable/Tallycode/ballots.txt): 
   ```OCaml 
   ciphertext = (1194, 2655) proof = {announcement = (3967, 1580), (1535, 1972); challenge = 2446, 1626, 820; response = 2938, 2178};  ciphertext = (2534, 746) proof = {announcement = (5583, 624), (4008, 5083); challenge = 1851, 167, 1684; response = 891, 410};  ciphertext = (1282, 3528) proof = {announcement = (4452, 972), (4164, 430); challenge = 1144, 98, 1046; response = 205, 486};  ciphertext = (421, 1602) proof = {announcement = (929, 2474), (5515, 3442); challenge = 2490, 2022, 468; response = 2871, 1380};  ciphertext = (2341, 3598) proof = {announcement = (1312, 2677), (4279, 2694); challenge = 1920, 1922, 2961; response = 2783, 1161};  ciphertext = (5616, 3441) proof = {announcement = (456, 2833), (5717, 4450); challenge = 2339, 1749, 590; response = 1057, 1060};  ciphertext = (4390, 900) proof = {announcement = (2826, 5202), (242, 5517); challenge = 1926, 2656, 2233; response = 2742, 1166};  ciphertext = (2977, 2403) proof = {announcement = (5184, 5776), (1029, 4329); challenge = 480, 645, 2798; response = 2338, 2480};  ciphertext = (4726, 4116) proof = {announcement = (1684, 3711), (1393, 5451); challenge = 1682, 1997, 2648; response = 2833, 859};  ciphertext = (3745, 2815) proof = {announcement = (3009, 3807), (2223, 3698); challenge = 1792, 309, 1483; response = 2511, 1063}
   ciphertext = (6, 762) proof = {announcement = (911, 4788), (4384, 4536); challenge = 1791, 1583, 208; response = 2673, 2449};  ciphertext = (399, 4310) proof = {announcement = (186, 1369), (5297, 2366); challenge = 1805, 725, 1080; response = 733, 459};  ciphertext = (5399, 4029) proof = {announcement = (2547, 1255), (985, 1380); challenge = 1549, 1270, 279; response = 2840, 567};  ciphertext = (1429, 5621) proof = {announcement = (4858, 2601), (5135, 2070); challenge = 2442, 2943, 2462; response = 495, 1414};  ciphertext = (2042, 2187) proof = {announcement = (1070, 4614), (4501, 2785); challenge = 2355, 2488, 2830; response = 1137, 669};  ciphertext = (2243, 4098) proof = {announcement = (2677, 2038), (4847, 4647); challenge = 2955, 633, 2322; response = 2149, 2107};  ciphertext = (2440, 659) proof = {announcement = (98, 2649), (729, 2024); challenge = 2645, 818, 1827; response = 2258, 1894};  ciphertext = (4026, 2492) proof = {announcement = (283, 3084), (3325, 5488); challenge = 890, 2529, 1324; response = 525, 2839};  ciphertext = (5876, 686) proof = {announcement = (2, 1792), (5619, 110); challenge = 713, 1717, 1959; response = 1039, 1341};  ciphertext = (5606, 4692) proof = {announcement = (1009, 4777), (5824, 1950); challenge = 1487, 2338, 2112; response = 1165, 914}
   .....
   .....
   (* 200 ballot,*)
   ```
10. Run `dune exec _build/default/src/Executable/Tallycode/main.exe <  src/Executable/Tallycode/ballots.txt` to run the Tallying code. You will see an output like [this](/src/Executable/Tallycode/output.txt).
   ```OCaml
   Encrypted zero-tally : (2938, 2744)  (5725, 1158)  (5281, 5396)  (2421, 1163)  (2750, 3100)  (1897, 3541)  (5646, 883)  (5605, 5221)  (3591, 3962)  (2136, 4175)
   Decrypted zero-tally (g^0) : 1  1  1  1  1  1  1  1  1  1
   Decryption zero-knowledge proof : proof = {announcement = 5538, 1819; challenge = 1802; response = 1258}  proof = {announcement = 5650, 4057; challenge = 1294; response = 1776}  proof = {announcement = 3032, 4736; challenge = 2067; response = 264}  proof = {announcement = 1021, 722; challenge = 1041; response = 601}  proof = {announcement = 2946, 351; challenge = 2887; response = 2281}  proof = {announcement = 5400, 3976; challenge = 2653; response = 1805}  proof = {announcement = 4023, 4032; challenge = 2506; response = 1573}  proof = {announcement = 4759, 2128; challenge = 2769; response = 5}  proof = {announcement = 4262, 3513; challenge = 59; response = 1219}  proof = {announcement = 186, 369; challenge = 2734; response = 947}
   ------------------------------------------------------------------------------------------------------------------------------------------------------
   Valid ballot : ciphertext = (1194, 2655) proof = {announcement = (3967, 1580), (1535, 1972); challenge = 2446, 1626, 820; response = 2938, 2178}  ciphertext = (2534, 746) proof = {announcement = (5583, 624), (4008, 5083); challenge = 1851, 167, 1684; response = 891, 410}  ciphertext = (1282, 3528) proof = {announcement = (4452, 972), (4164, 430); challenge = 1144, 98, 1046; response = 205, 486}  ciphertext = (421, 1602) proof = {announcement = (929, 2474), (5515, 3442); challenge = 2490, 2022, 468; response = 2871, 1380}  ciphertext = (2341, 3598) proof = {announcement = (1312, 2677), (4279, 2694); challenge = 1920, 1922, 2961; response = 2783, 1161}  ciphertext = (5616, 3441) proof = {announcement = (456, 2833), (5717, 4450); challenge = 2339, 1749, 590; response = 1057, 1060}  ciphertext = (4390, 900) proof = {announcement = (2826, 5202), (242, 5517); challenge = 1926, 2656, 2233; response = 2742, 1166}  ciphertext = (2977, 2403) proof = {announcement = (5184, 5776), (1029, 4329); challenge = 480, 645, 2798; response = 2338, 2480}  ciphertext = (4726, 4116) proof = {announcement = (1684, 3711), (1393, 5451); challenge = 1682, 1997, 2648; response = 2833, 859}  ciphertext = (3745, 2815) proof = {announcement = (3009, 3807), (2223, 3698); challenge = 1792, 309, 1483; response = 2511, 1063} 
   Previous tally : (2938, 2744)  (5725, 1158)  (5281, 5396)  (2421, 1163)  (2750, 3100)  (1897, 3541)  (5646, 883)  (5605, 5221)  (3591, 3962)  (2136, 4175)
   Current tally : (5115, 1037)  (3781, 4453)  (1608, 5491)  (5724, 2048)  (1028, 5113)  (2733, 4596)  (5153, 482)  (1580, 4531)  (2065, 2415)  (3797, 5311)
   ------------------------------------------------------------------------------------------------------------------------------------------------------
   Invalid ballot : ciphertext = (6, 762) proof = {announcement = (911, 4788), (4384, 4536); challenge = 1791, 1583, 208; response = 2673, 2449}  ciphertext = (399, 4310) proof = {announcement = (186, 1369), (5297, 2366); challenge = 1805, 725, 1080; response = 733, 459}  ciphertext = (5399, 4029) proof = {announcement = (2547, 1255), (985, 1380); challenge = 1549, 1270, 279; response = 2840, 567}  ciphertext = (1429, 5621) proof = {announcement = (4858, 2601), (5135, 2070); challenge = 2442, 2943, 2462; response = 495, 1414}  ciphertext = (2042, 2187) proof = {announcement = (1070, 4614), (4501, 2785); challenge = 2355, 2488, 2830; response = 1137, 669}  ciphertext = (2243, 4098) proof = {announcement = (2677, 2038), (4847, 4647); challenge = 2955, 633, 2322; response = 2149, 2107}  ciphertext = (2440, 659) proof = {announcement = (98, 2649), (729, 2024); challenge = 2645, 818, 1827; response = 2258, 1894}  ciphertext = (4026, 2492) proof = {announcement = (283, 3084), (3325, 5488); challenge = 890, 2529, 1324; response = 525, 2839}  ciphertext = (5876, 686) proof = {announcement = (2, 1792), (5619, 110); challenge = 713, 1717, 1959; response = 1039, 1341}  ciphertext = (5606, 4692) proof = {announcement = (1009, 4777), (5824, 1950); challenge = 1487, 2338, 2112; response = 1165, 914} 
   Previous tally : (5115, 1037)  (3781, 4453)  (1608, 5491)  (5724, 2048)  (1028, 5113)  (2733, 4596)  (5153, 482)  (1580, 4531)  (2065, 2415)  (3797, 5311)
   Current tally : (5115, 1037)  (3781, 4453)  (1608, 5491)  (5724, 2048)  (1028, 5113)  (2733, 4596)  (5153, 482)  (1580, 4531)  (2065, 2415)  (3797, 5311)
   ------------------------------------------------------------------------------------------------------------------------------------------------------
   Valid ballot : ciphertext = (1444, 772) proof = {announcement = (2990, 4776), (758, 3428); challenge = 375, 2124, 1214; response = 1242, 2726}  ciphertext = (3010, 2269) proof = {announcement = (624, 3519), (2742, 4704); challenge = 519, 1149, 2333; response = 1014, 1637}  ciphertext = (4269, 4155) proof = {announcement = (1072, 5375), (398, 5910); challenge = 234, 2448, 749; response = 512, 363}  ciphertext = (2344, 4739) proof = {announcement = (5107, 2549), (700, 3618); challenge = 631, 2912, 682; response = 963, 1707}  ciphertext = (4782, 5748) proof = {announcement = (3083, 4505), (1673, 2845); challenge = 1158, 1482, 2639; response = 1788, 2405}  ciphertext = (3257, 5509) proof = {announcement = (3517, 1817), (5103, 1922); challenge = 1507, 2571, 1899; response = 2647, 638}  ciphertext = (5488, 1994) proof = {announcement = (1900, 32), (1007, 3374); challenge = 1972, 1753, 219; response = 278, 2250}  ciphertext = (997, 56) proof = {announcement = (3927, 47), (4047, 879); challenge = 309, 1584, 1688; response = 306, 1482}  ciphertext = (2841, 5513) proof = {announcement = (3339, 956), (3723, 4796); challenge = 1601, 2200, 2364; response = 2677, 2230}  ciphertext = (1213, 290) proof = {announcement = (1169, 1194), (4613, 4610); challenge = 2811, 1447, 1364; response = 131, 2018} 
   Previous tally : (5115, 1037)  (3781, 4453)  (1608, 5491)  (5724, 2048)  (1028, 5113)  (2733, 4596)  (5153, 482)  (1580, 4531)  (2065, 2415)  (3797, 5311)
   Current tally : (1018, 419)  (970, 4249)  (1086, 2082)  (4255, 2973)  (2413, 3458)  (4954, 5147)  (1947, 934)  (4605, 4802)  (4862, 1853)  (482, 5097)
   .....
   .....
   (* more lines *)
   ```