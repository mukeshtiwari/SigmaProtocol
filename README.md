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
9. Run `dune exec _build/default/src/Executable/Approvalcode/main.exe` to run the Approval voting. You will see an output like [this](/src/Executable/Approvalcode/ballots.txt): 
   ```OCaml 
   ciphertext = (1194, 2655) proof = {announcement = (3967, 1580), (1535, 1972); challenge = 2446, 1626, 820; response = 2938, 2178};  ciphertext = (2534, 746) proof = {announcement = (5583, 624), (4008, 5083); challenge = 1851, 167, 1684; response = 891, 410};  ciphertext = (1282, 3528) proof = {announcement = (4452, 972), (4164, 430); challenge = 1144, 98, 1046; response = 205, 486};  ciphertext = (421, 1602) proof = {announcement = (929, 2474), (5515, 3442); challenge = 2490, 2022, 468; response = 2871, 1380};  ciphertext = (2341, 3598) proof = {announcement = (1312, 2677), (4279, 2694); challenge = 1920, 1922, 2961; response = 2783, 1161};  ciphertext = (5616, 3441) proof = {announcement = (456, 2833), (5717, 4450); challenge = 2339, 1749, 590; response = 1057, 1060};  ciphertext = (4390, 900) proof = {announcement = (2826, 5202), (242, 5517); challenge = 1926, 2656, 2233; response = 2742, 1166};  ciphertext = (2977, 2403) proof = {announcement = (5184, 5776), (1029, 4329); challenge = 480, 645, 2798; response = 2338, 2480};  ciphertext = (4726, 4116) proof = {announcement = (1684, 3711), (1393, 5451); challenge = 1682, 1997, 2648; response = 2833, 859};  ciphertext = (3745, 2815) proof = {announcement = (3009, 3807), (2223, 3698); challenge = 1792, 309, 1483; response = 2511, 1063}
   ciphertext = (6, 762) proof = {announcement = (911, 4788), (4384, 4536); challenge = 1791, 1583, 208; response = 2673, 2449};  ciphertext = (399, 4310) proof = {announcement = (186, 1369), (5297, 2366); challenge = 1805, 725, 1080; response = 733, 459};  ciphertext = (5399, 4029) proof = {announcement = (2547, 1255), (985, 1380); challenge = 1549, 1270, 279; response = 2840, 567};  ciphertext = (1429, 5621) proof = {announcement = (4858, 2601), (5135, 2070); challenge = 2442, 2943, 2462; response = 495, 1414};  ciphertext = (2042, 2187) proof = {announcement = (1070, 4614), (4501, 2785); challenge = 2355, 2488, 2830; response = 1137, 669};  ciphertext = (2243, 4098) proof = {announcement = (2677, 2038), (4847, 4647); challenge = 2955, 633, 2322; response = 2149, 2107};  ciphertext = (2440, 659) proof = {announcement = (98, 2649), (729, 2024); challenge = 2645, 818, 1827; response = 2258, 1894};  ciphertext = (4026, 2492) proof = {announcement = (283, 3084), (3325, 5488); challenge = 890, 2529, 1324; response = 525, 2839};  ciphertext = (5876, 686) proof = {announcement = (2, 1792), (5619, 110); challenge = 713, 1717, 1959; response = 1039, 1341};  ciphertext = (5606, 4692) proof = {announcement = (1009, 4777), (5824, 1950); challenge = 1487, 2338, 2112; response = 1165, 914}
   .....
   .....
   (* 200 ballot,*)
   ```
10. Run `dune exec _build/default/src/Executable/Tallycode/main.exe <  src/Executable/Approvalcode/ballots.txt` to run the Tallying code. You will see an output like [this](/src/Executable/Tallycode/output.txt).
   ```OCaml
   Identity-tally : (1, 1)  (1, 1)  (1, 1)  (1, 1)  (1, 1)  (1, 1)  (1, 1)  (1, 1)  (1, 1)  (1, 1)
   ------------------------------------------------------------------------------------------------------------------------------------------------------
   Valid ballot : ciphertext = (5193, 1918) proof = {announcement = (4932, 4849), (5723, 4121); challenge = 1563, 1422, 141; response = 227, 1027}  ciphertext = (1122, 2087) proof = {announcement = (4533, 2210), (3516, 4796); challenge = 2456, 2352, 104; response = 124, 1020}  ciphertext = (3552, 1734) proof = {announcement = (3100, 1175), (747, 2825); challenge = 838, 763, 75; response = 2300, 1282}  ciphertext = (3932, 4988) proof = {announcement = (1283, 2363), (4509, 4457); challenge = 546, 2594, 915; response = 738, 1939}  ciphertext = (193, 2319) proof = {announcement = (1175, 5184), (956, 1010); challenge = 816, 2811, 968; response = 810, 2505}  ciphertext = (4455, 385) proof = {announcement = (5887, 3582), (4548, 4101); challenge = 382, 1274, 2071; response = 2806, 142}  ciphertext = (5792, 934) proof = {announcement = (435, 89), (485, 1200); challenge = 61, 916, 2108; response = 1021, 1971}  ciphertext = (870, 4107) proof = {announcement = (5283, 5696), (3188, 4803); challenge = 1413, 1922, 2454; response = 2351, 447}  ciphertext = (3423, 982) proof = {announcement = (4434, 3064), (1651, 4846); challenge = 775, 379, 396; response = 1883, 471}  ciphertext = (2603, 5533) proof = {announcement = (4762, 5253), (819, 628); challenge = 1845, 2486, 2322; response = 2408, 693} 
   Previous tally : (1, 1)  (1, 1)  (1, 1)  (1, 1)  (1, 1)  (1, 1)  (1, 1)  (1, 1)  (1, 1)  (1, 1)
   Current tally : (5193, 1918)  (1122, 2087)  (3552, 1734)  (3932, 4988)  (193, 2319)  (4455, 385)  (5792, 934)  (870, 4107)  (3423, 982)  (2603, 5533)
   ------------------------------------------------------------------------------------------------------------------------------------------------------
   Invalid ballot : ciphertext = (4111, 2308) proof = {announcement = (3806, 4259), (391, 2004); challenge = 1044, 883, 161; response = 1105, 1850}  ciphertext = (4034, 3532) proof = {announcement = (5755, 312), (4797, 1754); challenge = 2689, 1773, 916; response = 63, 2754}  ciphertext = (991, 2231) proof = {announcement = (457, 4628), (1096, 5729); challenge = 117, 2944, 136; response = 2653, 839}  ciphertext = (5073, 5427) proof = {announcement = (2952, 804), (2601, 2428); challenge = 1509, 1328, 181; response = 2547, 1846}  ciphertext = (4871, 331) proof = {announcement = (3244, 4076), (2412, 2287); challenge = 472, 1973, 1462; response = 1837, 998}  ciphertext = (2780, 5791) proof = {announcement = (1177, 3087), (2859, 3881); challenge = 64, 2649, 378; response = 269, 2289}  ciphertext = (4370, 1485) proof = {announcement = (2615, 362), (363, 3763); challenge = 2554, 1113, 1441; response = 160, 847}  ciphertext = (4098, 2705) proof = {announcement = (1726, 5229), (2534, 746); challenge = 563, 955, 2571; response = 1551, 1930}  ciphertext = (1542, 1760) proof = {announcement = (1992, 1993), (3220, 1573); challenge = 1929, 2147, 2745; response = 2865, 1107}  ciphertext = (867, 340) proof = {announcement = (759, 1582), (83, 5750); challenge = 1759, 1596, 163; response = 2904, 1551} 
   Previous tally : (5193, 1918)  (1122, 2087)  (3552, 1734)  (3932, 4988)  (193, 2319)  (4455, 385)  (5792, 934)  (870, 4107)  (3423, 982)  (2603, 5533)
   Current tally : (5193, 1918)  (1122, 2087)  (3552, 1734)  (3932, 4988)  (193, 2319)  (4455, 385)  (5792, 934)  (870, 4107)  (3423, 982)  (2603, 5533)
   ------------------------------------------------------------------------------------------------------------------------------------------------------
   Valid ballot : ciphertext = (2184, 3447) proof = {announcement = (4826, 2473), (5358, 2888); challenge = 225, 653, 2535; response = 1412, 23}  ciphertext = (3800, 5830) proof = {announcement = (638, 1523), (1992, 1642); challenge = 300, 2785, 478; response = 1804, 945}  ciphertext = (5046, 3550) proof = {announcement = (3502, 2169), (4270, 3369); challenge = 2370, 1824, 546; response = 2266, 2471}  ciphertext = (5797, 1133) proof = {announcement = (5371, 2158), (3325, 5488); challenge = 2306, 1453, 853; response = 610, 2130}  ciphertext = (1199, 4726) proof = {announcement = (1398, 14), (4958, 4888); challenge = 1174, 1385, 2752; response = 222, 264}  ciphertext = (1084, 1092) proof = {announcement = (4346, 3153), (871, 2463); challenge = 1769, 1861, 2871; response = 1516, 1584}  ciphertext = (1053, 2035) proof = {announcement = (5533, 3351), (3965, 3868); challenge = 1867, 1854, 13; response = 2281, 2879}  ciphertext = (726, 4337) proof = {announcement = (2185, 4265), (3721, 1378); challenge = 2536, 1499, 1037; response = 981, 1056}  ciphertext = (4023, 4426) proof = {announcement = (3744, 515), (339, 2169); challenge = 461, 1520, 1904; response = 1705, 2456}  ciphertext = (805, 2495) proof = {announcement = (3627, 1739), (1883, 1156); challenge = 1421, 2121, 2263; response = 955, 1041} 
   Previous tally : (5193, 1918)  (1122, 2087)  (3552, 1734)  (3932, 4988)  (193, 2319)  (4455, 385)  (5792, 934)  (870, 4107)  (3423, 982)  (2603, 5533)
   Current tally : (3161, 2741)  (2087, 5006)  (144, 3474)  (4489, 2973)  (254, 571)  (4642, 5530)  (93, 4050)  (3358, 1424)  (2308, 1841)  (3184, 852)
   ------------------------------------------------------------------------------------------------------------------------------------------------------
   Invalid ballot : ciphertext = (4060, 1917) proof = {announcement = (3305, 5476), (2056, 2006); challenge = 215, 2094, 1084; response = 2442, 703}  ciphertext = (494, 25) proof = {announcement = (48, 5722), (4548, 4101); challenge = 2119, 1637, 482; response = 892, 35}  ciphertext = (3155, 4789) proof = {announcement = (440, 4356), (5509, 5383); challenge = 443, 2216, 1190; response = 2557, 139}  ciphertext = (2394, 742) proof = {announcement = (1152, 1503), (4683, 3609); challenge = 1077, 214, 863; response = 1542, 332}  ciphertext = (170, 3163) proof = {announcement = (888, 529), (4731, 2672); challenge = 1900, 202, 1698; response = 1400, 1261}  ciphertext = (4652, 1390) proof = {announcement = (5094, 3343), (2075, 4031); challenge = 23, 230, 2756; response = 707, 230}  ciphertext = (2337, 4121) proof = {announcement = (613, 5014), (2141, 3545); challenge = 2920, 762, 2158; response = 84, 2049}  ciphertext = (827, 2201) proof = {announcement = (741, 4310), (2417, 3868); challenge = 501, 1443, 2021; response = 1053, 132}  ciphertext = (145, 5561) proof = {announcement = (5270, 4746), (2440, 5295); challenge = 2686, 2497, 189; response = 1366, 2890}  ciphertext = (4572, 1754) proof = {announcement = (5248, 2352), (5866, 3010); challenge = 101, 410, 2654; response = 669, 1790} 
   Previous tally : (3161, 2741)  (2087, 5006)  (144, 3474)  (4489, 2973)  (254, 571)  (4642, 5530)  (93, 4050)  (3358, 1424)  (2308, 1841)  (3184, 852)
   Current tally : (3161, 2741)  (2087, 5006)  (144, 3474)  (4489, 2973)  (254, 571)  (4642, 5530)  (93, 4050)  (3358, 1424)  (2308, 1841)  (3184, 852)
   .....
   .....
   (* more lines *)
   ```
11. Run `dune exec _build/default/src/Executable/DistElgamalcode/main.exe` to run the Distributed Elgamal code. You will see an output like this: 
   ```OCaml
   Original messages: [2185, 159, 409, 2552, 2649, 1893, 649, 1227, 685, 2455]
   Ciphertexts: [(4824, 378), (4617, 385), (379, 791), (1014, 201), (1964, 5245), (3214, 5550), (215, 1641), (3426, 4870), (5708, 4867), (3553, 1444)]
   First decryption factors: [489, 2319, 444, 1809, 3900, 4238, 4723, 1861, 5112, 4614]
   Second decryption factors: [5103, 5093, 2084, 1351, 5306, 5887, 5557, 5912, 350, 1728]
   Third decryption factors: [1037, 852, 4709, 5514, 4380, 3038, 2072, 5322, 1086, 3707]
   Decrypted messages: [2185, 159, 409, 2552, 2649, 1893, 649, 1227, 685, 2455]
   ```
12. Run `dune exec _build/default/src/Executable/ChaumPedersencode/main.exe` to run the Chaum-Pedersen code. You will see an output like this:
   ```OCaml
   p = 5927, q = 2963, g = 4, h = 7
   proof = {annoucement = 1944, 2503 challenge = 721 response = 2482}
   true%
   ```