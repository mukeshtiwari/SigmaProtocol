// Honest ballots from the Helios booth's own JavaScript (heliosbooth/js of
// the pinned helios-server: jsbn, sjcl, elgamal.js, sha1.js), loaded as
// bench/bench_helios_js.js does. The booth draws its randomness internally
// (sjcl), so its outputs are not reproducible: run.sh saves them as fixtures
// (fixtures/booth.json) and only regenerates them on request.
//
// stdin:  {"elections": [{"name", "p", "q", "g", "y", "votes": [[0|1, ...], ...]}, ...]}
// stdout: {"<name>": [{"choices": [{alpha, beta}], "individual_proofs": [[{challenge, commitment: {A, B}, response}, x2]]}, ...]}
const fs = require('fs'), vm = require('vm'), crypto = require('crypto');
const DIR = __dirname + '/../helios-server/heliosbooth/js';
const ctx = { console, navigator: { appName: 'Netscape' }, window: {}, alert: (m) => { throw new Error('alert: ' + m); } };
ctx.globalThis = ctx;
vm.createContext(ctx);
for (const f of ['jscrypto/class.js', 'jscrypto/jsbn.js', 'jscrypto/jsbn2.js', 'jscrypto/sjcl.js', 'underscore-min.js',
                 'jscrypto/bigint.js', 'jscrypto/random.js', 'jscrypto/elgamal.js', 'jscrypto/sha1.js'])
  vm.runInContext(fs.readFileSync(DIR + '/' + f, 'utf8'), ctx, { filename: f });
vm.runInContext(`sjcl.random.addEntropy("${crypto.randomBytes(128).toString('hex')}", 1024, "node");`, ctx);
vm.runInContext(`
  function boothBallot(p, q, g, y, votes) {
    var pk = new ElGamal.PublicKey(new BigInt(p, 10), new BigInt(q, 10), new BigInt(g, 10), new BigInt(y, 10));
    var pts = [new ElGamal.Plaintext(BigInt.ONE, pk, false), new ElGamal.Plaintext(pk.g, pk, false)];
    var choices = [], proofs = [];
    for (var i = 0; i < votes.length; i++) {
      var r = Random.getRandomInteger(pk.q);
      var ct = ElGamal.encrypt(pk, pts[votes[i]], r);
      var dp = ct.generateDisjunctiveProof(pts, votes[i], r, ElGamal.disjunctive_challenge_generator);
      choices.push({alpha: ct.alpha.toString(), beta: ct.beta.toString()});
      proofs.push(dp.proofs.map(function (pr) {
        return {challenge: pr.challenge.toString(), commitment: {A: pr.commitment.A.toString(), B: pr.commitment.B.toString()},
                response: pr.response.toString()};
      }));
    }
    return {choices: choices, individual_proofs: proofs};
  }`, ctx);
const input = JSON.parse(fs.readFileSync(0, 'utf8'));
const out = {};
for (const e of input.elections)
  out[e.name] = e.votes.map(v => vm.runInContext(`boothBallot(${JSON.stringify(e.p)}, ${JSON.stringify(e.q)}, ${JSON.stringify(e.g)}, ${JSON.stringify(e.y)}, ${JSON.stringify(v)})`, ctx));
process.stdout.write(JSON.stringify(out));
