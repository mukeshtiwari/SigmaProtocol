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

2. Run `dune exec _build/default/src/Executable/Sigmacode/main.exe` to run the sigma protocol. You will see output like this:
   ```OCaml
   (base) mukesh.tiwari@Mukeshs-MacBook-Pro-2 SigmaProtocol % dune exec _build/default/src/Executable/Sigmacode/main.exe
    p = 5927, q = 2963, g = 4, h = 64
    proof = {annoucement = 1644,  challenge = 1987,  response = 2269, }
    true%
    ```
3. Run `dune exec _build/default/src/Executable/AndSigmacode/main.exe` to run the AndSigma protocol. You will see output like this:
   ```OCaml
   (base) mukesh.tiwari@Mukeshs-MacBook-Pro-2 SigmaProtocol % dune exec _build/default/src/Executable/AndSigmacode/main.exe
    p = 5927, q = 2963, g = 4, h1 = 64, h2 = 1024, h3 = 339
    proof = {annoucement = 2036, 2070, 3797,  challenge = 461,  response = 1709, 1298, 722, }
    true%
   ```
4. Run `dune exec _build/default/src/Executable/ParaSigmacode/main.exe` to run the Parallel Sigma protocol. You will see output like this:
   ```OCaml
   (base) mukesh.tiwari@Mukeshs-MacBook-Pro-2 SigmaProtocol % dune exec _build/default/src/Executable/ParaSigmacode/main.exe
    p = 5927, q = 2963, g = 4, h = 64
    proof = {annoucement = 4823, 4334,  challenge = 2303, 2717,  response = 2634, 1787, }
    true%
   ```
5. Run `dune exec _build/default/src/Executable/Elgamalcode/main.exe` to run the Elgamal encryption functions. You will see output like this: 
   ```OCaml
   (base) mukesh.tiwari@Mukeshs-MacBook-Pro-2 SigmaProtocol % dune exec _build/default/src/Executable/Elgamalcode/main.exe
   message ms1 = 1438, 2189, 1367, 2838, 1976, 1242, 1293, 547, 318, 1642
   encryption cs1 = (772, 982), (3598, 4290), (5616, 1176), (5606, 4148), (3815, 4574), (513, 21), (254, 2913), (5742, 588), (1318, 5099), (5253, 1443)
   decryption ds1 = 999969, 997757, 999898, 998406, 997544, 999773, 999824, 999078, 998849, 997210
   rencryption cs2 = (4238, 3122), (4202, 1029), (3807, 956), (3457, 5530), (4516, 331), (1267, 4202), (2610, 3111), (4665, 800), (3235, 145), (289, 3627)
   decryption ds2 = 999969, 997757, 999898, 998406, 997544, 999773, 999824, 999078, 998849, 997210
   multiplication enc ballot cs3 = (32, 1545), (4946, 4722), (1423, 4053), (4579, 950), (4678, 2609), (3928, 5264), (5043, 5887), (2317, 2167), (2217, 4407), (805, 220)
   decryption ds3 = 998444, 999946, 998302, 998281, 999520, 998052, 998154, 999625, 999167, 998852%
   ```
6. Run `dune exec _build/default/src/Executable/OrSigmacode/main.exe` to run the OR Sigma protocol. You will see output like this:
   ```OCaml 
   (base) mukesh.tiwari@Mukeshs-MacBook-Pro-2 SigmaProtocol % dune exec _build/default/src/Executable/OrSigmacode/main.exe
   p = 5927, q = 2963, g = 4, h_UU2081_  = 12, h_UU2082_  = 64, h_UU2083_  = 25, com = 3173, 1573, 1351,
   proof = {annoucement = 3173, 1573, 1351,  challenge = 1723, 1429, 2530, 727,  response = 455, 2825, 1712, }
   true%
   ```
7. Run `dune exec _build/default/src/Executable/EncProofcode/main.exe` to run the Encryption Proof Sigma protocol. You will see output like this: 
   ```OCaml
   (base) mukesh.tiwari@Mukeshs-MacBook-Pro-2 SigmaProtocol % dune exec _build/default/src/Executable/EncProofcode/main.exe
   p = 5927, q = 2963, g = 12, h  = 25, m_UU2080_  = 28, m_UU2081_  = 134, m_UU2082_ = 38, cp = (3108, 450), com = (83, 5583), (4551, 5153), (72, 586)
   proof = {annoucement = (83, 5583), (3021, 5294), (3534, 677) challenge = 2026, 2515, 1078, 1396 response = 1448, 228, 2263}
   true%
   ```