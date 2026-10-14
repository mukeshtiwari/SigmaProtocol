The `allAvailableJson` test record of electionguard-kotlin-multiplatform
(https://github.com/JohnLCaron/electionguard-kotlin-multiplatform,
`egklib/src/commonTest/data/workflow/allAvailableJson`, MIT licence): an
ElectionGuard 2.0 election record with three guardians (quorum 3), a
manifest of 20 contests of 5 options each, 11 cast ballots, the encrypted
tally and its decryption. The record's private data (plaintext ballots and
the guardians' keys) is not included. The `chainedJson` record of the same
directory, with chained confirmation codes and three challenged ballots,
verifies the same way (`main.exe DIRECTORY`).
