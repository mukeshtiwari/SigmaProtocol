A Belenios 3.2.0 election on Ed25519 generated with `tests/tool/demo.sh`
of the Belenios sources: five weighted voters, two questions (one with
a blank vote), three revotes, three "Single" trustees. `ve3KB6dyuh66fD.bel`
is the public-data archive; `ve3KB6dyuh66fD.private_creds.txt` holds the
voters' private credentials, which `bench/belenios_tamper.py` uses to
produce validly signed but invalid ballots for testing the verifier.

Two larger elections, generated the same way and used for the benchmark
table in `bench/README.md`: `eyo1Ps3KrSKYJy.bel` (`demo-n-voters.sh` with
`num_voters=300`: 300 voters, the same two questions) and
`JDMgPNJoVM6ZuT.bel` (`demo-complex.sh`: 10 voters, three questions with
8, 131 and 19 answers). Their `*.private_creds.txt` files serve the same
purpose as above.
