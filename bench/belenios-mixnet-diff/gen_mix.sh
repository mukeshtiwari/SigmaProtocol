#!/bin/bash
# Generates one non-homomorphic (mix-net) Belenios election with belenios-tool,
# following tests/tool/demo-nh.sh of the pinned release: Ed25519, two "Single"
# trustees, one homomorphic and one NonHomomorphic question, three ballots, two
# shuffles, decryption and result, then belenios-tool's own verification.
# Writes OUTDIR/{e.bel, trustee*.privkey}. Not reproducible bit for bit
# (belenios-tool reads /dev/urandom), so e.bel is kept as a fixture.
#
# usage: gen_mix.sh BELENIOS_TOOL OUTDIR
set -euo pipefail
TOOL=$(cd "$(dirname "$1")" && pwd)/$(basename "$1"); DIR=$2
mkdir -p "$DIR"; cd "$DIR"
export BELENIOS_USE_URANDOM=1
bt () { "$TOOL" "$@"; }
UUID=$(bt setup generate-token)
group="--group Ed25519"
bt setup generate-credentials --uuid "$UUID" $group --count 3 > /dev/null
mv ./*.pubcreds public_creds.json; mv ./*.privcreds private_creds.json
paste <(jq -r 'keys_unsorted[]' < private_creds.json) <(jq -r '.[]' < private_creds.json) > pc.txt
bt setup generate-trustee-key $group; bt setup generate-trustee-key $group
cat ./*.pubkey > public_keys.jsons; bt setup make-trustees
cat > t.json <<'EOF'
{"description":"d","name":"n","questions":[{"answers":["a","b"],"min":0,"max":1,"question":"q1"},{"type":"NonHomomorphic","value":{"answers":["A","B","C"],"question":"q3"}}]}
EOF
bt setup make-election --uuid "$UUID" $group --template t.json
bt archive init
rm -f election.json trustees.json public_creds.json public_keys.jsons
i=0
while IFS=$'\t' read -r id cred; do
    i=$((i + 1))
    bt election generate-ballot --privcred <(echo "$cred") --choice <(echo "[[1,0],[$i,2,3]]") | bt archive add-event --type=Ballot
done < pc.txt
bt archive add-event --type=EndBallots < /dev/null
bt election compute-encrypted-tally | bt archive add-event --type=EncryptedTally
bt election shuffle --trustee-id=1 | bt archive add-event --type=Shuffle
bt election shuffle --trustee-id=2 | bt archive add-event --type=Shuffle
bt archive add-event --type=EndShuffles < /dev/null
t=1
for u in $(ls ./*.privkey | sort); do
    bt election decrypt --privkey "$u" --trustee-id $t | bt archive add-event --type=PartialDecryption
    mv "$u" "trustee$t.privkey"; t=$((t + 1))
done
bt election compute-result | bt archive add-event --type=Result
bt election verify
mv "$UUID.bel" e.bel
rm -f pc.txt private_creds.json t.json
echo "fixture: $UUID"
