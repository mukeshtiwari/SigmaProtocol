// Benchmark: the same ballot encryption + disjunctive 0/1 proofs as
// bench_helios_js.js (the Helios booth computation), but reimplemented with
// JavaScript's native BigInt instead of the booth's jsbn library.
// This isolates how much of the booth's cost is jsbn's pure-JS big-integer
// arithmetic versus the protocol itself. The protocol steps mirror
// heliosbooth/js/jscrypto/elgamal.js operation for operation:
//   - ElGamal.encrypt: alpha = g^r, beta = y^r * m mod p
//   - Proof.generate (real branch): A = g^w, B = y^w, response = w + x*c mod q
//   - Proof.simulate (fake branch): A = (alpha^c)^-1 * g^s, B = (bop^c)^-1 * y^s
//   - disjunctive_challenge_generator: SHA-1 over comma-joined decimal
//     commitment strings (A1,B1,A2,B2), interpreted as a hex integer
//   - verifyDisjunctiveProof: group-membership checks (alpha^q = beta^q = 1),
//     both verification equations per branch, and sum-of-challenges check.
const crypto = require('crypto');

// IACR / Helios 2024 election parameters (same as bench_helios_js.js).
const p = 16328632084933010002384055033805457329601614771185955389739167309086214800406465799038583634953752941675645562182498120750264980492381375579367675648771293800310370964745767014243638518442553823973482995267304044326777047662957480269391322789378384619428596446446984694306187644767462460965622580087564339212631775817895958409016676398975671266179637898557687317076177218843233150695157881061257053019133078545928983562221396313169622475509818442661047018436264806901023966236718367204710755935899013750306107738002364137917426595737403871114187750804346564731250609196846638183903982387884578266136503697493474682071n;
const q = 61329566248342901292543872769978950870633559608669337131139375508370458778917n;
const g = 14887492224963187634282421537186040801304008017743492304481737382571933937568724473847106029915040150784031882206090286938661464458896494215273989547889201144857352611058572236578734319505128042602372864570426550855201448111746579871811249114781674309062693442442368697449970648232621880001709535143047913661432883287150003429802392229361583608686643243349727791976247247948618930423866180410558458272606627111270040091203073580238905303994472202930783207472394578498507764703191288249547659899997131166130259700604433891232298182348403175947450284433411265966789131024573629546048637848902243503970966798589660808533n;
const y = 7046735122051745594868985795786176392951854019485729367165971776021501311096201521482383017242860186177215354508901537446984239682993203747271798136868016921883953390308299741287014686008274215001426444189972901892121945650333202105534018888882197552388434304153312708859768386971193915314738375008791798536164901595463713712574129466783480981077498017586306273866594394401039338841105927980179401433149438028686338492134818995843560711439253445043076178166622915392760675509176356257990398772342230639242314592068285808565623831103115873314006496120730338309413064358649726464219249576117734308027594482849210379533n;

// square-and-multiply modular exponentiation (native BigInt has no modpow)
function modpow(base, exp, mod) {
  let result = 1n, b = base % mod, e = exp;
  while (e > 0n) {
    if (e & 1n) result = (result * b) % mod;
    b = (b * b) % mod;
    e >>= 1n;
  }
  return result;
}

// modular inverse via extended Euclid (jsbn's modInverse is the same algorithm)
function modinv(a, m) {
  let [old_r, r] = [((a % m) + m) % m, m];
  let [old_s, s] = [1n, 0n];
  while (r !== 0n) {
    const qt = old_r / r;
    [old_r, r] = [r, old_r - qt * r];
    [old_s, s] = [s, old_s - qt * s];
  }
  return ((old_s % m) + m) % m;
}

// uniform random integer below bound (mirrors Random.getRandomInteger)
function randBelow(bound) {
  const bytes = Math.ceil(bound.toString(2).length / 8) + 8;
  const x = BigInt('0x' + crypto.randomBytes(bytes).toString('hex'));
  return x % bound;
}

// SHA-1 challenge over comma-joined decimal commitment strings, as in
// ElGamal.disjunctive_challenge_generator
function disjunctiveChallenge(commitments) {
  const parts = [];
  for (const c of commitments) { parts.push(c.A.toString()); parts.push(c.B.toString()); }
  const h = crypto.createHash('sha1').update(parts.join(',')).digest('hex');
  return BigInt('0x' + h);
}

// plaintexts for 0 and 1: [1, g] (the booth encodes vote m as g^m)
const pts = [1n, g];

function encryptVote(m) {
  const r = randBelow(q);
  const alpha = modpow(g, r, p);
  const beta = (modpow(y, r, p) * pts[m]) % p;

  // disjunctive proof, real branch = m, simulated branch = 1 - m
  const simIdx = 1 - m;
  // Proof.simulate for the fake branch (DH tuple g, y, alpha, beta/pt)
  const bopSim = (beta * modinv(pts[simIdx], p)) % p;
  const cSim = randBelow(q);
  const sSim = randBelow(q);
  const ASim = (modinv(modpow(alpha, cSim, p), p) * modpow(g, sSim, p)) % p;
  const BSim = (modinv(modpow(bopSim, cSim, p), p) * modpow(y, sSim, p)) % p;

  // Proof.generate for the real branch
  const w = randBelow(q);
  const AReal = modpow(g, w, p);
  const BReal = modpow(y, w, p);
  const commitments = m === 0
    ? [{ A: AReal, B: BReal }, { A: ASim, B: BSim }]
    : [{ A: ASim, B: BSim }, { A: AReal, B: BReal }];
  const disj = disjunctiveChallenge(commitments);
  const cReal = (((disj - cSim) % q) + q) % q;
  const sReal = (w + r * cReal) % q;

  const proofs = m === 0
    ? [{ A: AReal, B: BReal, c: cReal, s: sReal }, { A: ASim, B: BSim, c: cSim, s: sSim }]
    : [{ A: ASim, B: BSim, c: cSim, s: sSim }, { A: AReal, B: BReal, c: cReal, s: sReal }];
  return { alpha, beta, proofs };
}

function verifyVote(ct) {
  // checkGroupMembership
  const pm1 = p - 1n;
  if (ct.alpha === 1n || ct.alpha === pm1) return false;
  if (ct.beta === 1n || ct.beta === pm1) return false;
  if (modpow(ct.alpha, q, p) !== 1n) return false;
  if (modpow(ct.beta, q, p) !== 1n) return false;

  // per-branch verification equations (DH tuple g, y, alpha, beta/pt)
  for (let i = 0; i < 2; i++) {
    const pr = ct.proofs[i];
    const bop = (ct.beta * modinv(pts[i], p)) % p;
    const first = modpow(g, pr.s, p) === (modpow(ct.alpha, pr.c, p) * pr.A) % p;
    const second = modpow(y, pr.s, p) === (modpow(bop, pr.c, p) * pr.B) % p;
    if (!first || !second) return false;
  }

  // sum-of-challenges check against the recomputed SHA-1 challenge
  const expected = disjunctiveChallenge(ct.proofs.map(pr => ({ A: pr.A, B: pr.B })));
  const sum = (ct.proofs[0].c + ct.proofs[1].c) % q;
  return expected === sum;
}

function encryptBallot(n) {
  const ballot = [];
  for (let i = 0; i < n; i++) ballot.push(encryptVote(Math.random() < 0.5 ? 0 : 1));
  return ballot;
}

function verifyBallot(ballot) {
  let ok = true;
  for (const ct of ballot) ok = ok && verifyVote(ct);
  return ok;
}

const n = parseInt(process.argv[2] || '7', 10);
const iters = parseInt(process.argv[3] || '30', 10);

// warm-up
verifyBallot(encryptBallot(n));

const encT = [], verT = [];
let allOk = true;
for (let i = 0; i < iters; i++) {
  const t0 = process.hrtime.bigint();
  const ballot = encryptBallot(n);
  const t1 = process.hrtime.bigint();
  const ok = verifyBallot(ballot);
  const t2 = process.hrtime.bigint();
  allOk = allOk && ok;
  encT.push(Number(t1 - t0) / 1e6);
  verT.push(Number(t2 - t1) / 1e6);
}
const median = (a) => { const s = [...a].sort((x, y) => x - y); const l = s.length;
  return l % 2 ? s[(l - 1) / 2] : (s[l / 2 - 1] + s[l / 2]) / 2; };
const mean = (a) => a.reduce((x, y) => x + y, 0) / a.length;

console.log(`Helios protocol, native BigInt, n=${n}, iters=${iters}, all verified=${allOk}`);
console.log(`ballot encryption + proofs: median ${median(encT).toFixed(2)} ms, mean ${mean(encT).toFixed(2)} ms`);
console.log(`ballot verification:        median ${median(verT).toFixed(2)} ms, mean ${mean(verT).toFixed(2)} ms`);
