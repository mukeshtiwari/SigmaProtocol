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