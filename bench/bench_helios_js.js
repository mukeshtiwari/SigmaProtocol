// Benchmark: Helios booth hand-written JS (jsbn/sjcl) ballot encryption
// + disjunctive 0/1 proofs, at the IACR 2024 Helios parameters.
const fs = require('fs'), vm = require('vm'), crypto = require('crypto');

const DIR = __dirname + '/helios-server/heliosbooth/js';
const ctx = {
  console,
  navigator: { appName: 'Netscape' },
  window: {},
  alert: (m) => { throw new Error('alert: ' + m); },
};
ctx.globalThis = ctx;
vm.createContext(ctx);

for (const f of ['jscrypto/class.js', 'jscrypto/jsbn.js', 'jscrypto/jsbn2.js',
                 'jscrypto/sjcl.js', '../js/underscore-min.js'.replace('../js/',''),
                 'jscrypto/bigint.js', 'jscrypto/random.js',
                 'jscrypto/elgamal.js', 'jscrypto/sha1.js']) {
  const path = f === 'underscore-min.js' ? DIR + '/underscore-min.js' : DIR + '/' + f;
  vm.runInContext(fs.readFileSync(path, 'utf8'), ctx, { filename: f });
}

// Seed sjcl's PRNG from Node's CSPRNG.
vm.runInContext(`sjcl.random.addEntropy("${crypto.randomBytes(128).toString('hex')}", 1024, "node");`, ctx);

// IACR / Helios 2024 election parameters (same as HeliosTallyIns.v).
const p = '16328632084933010002384055033805457329601614771185955389739167309086214800406465799038583634953752941675645562182498120750264980492381375579367675648771293800310370964745767014243638518442553823973482995267304044326777047662957480269391322789378384619428596446446984694306187644767462460965622580087564339212631775817895958409016676398975671266179637898557687317076177218843233150695157881061257053019133078545928983562221396313169622475509818442661047018436264806901023966236718367204710755935899013750306107738002364137917426595737403871114187750804346564731250609196846638183903982387884578266136503697493474682071';
const q = '61329566248342901292543872769978950870633559608669337131139375508370458778917';
const g = '14887492224963187634282421537186040801304008017743492304481737382571933937568724473847106029915040150784031882206090286938661464458896494215273989547889201144857352611058572236578734319505128042602372864570426550855201448111746579871811249114781674309062693442442368697449970648232621880001709535143047913661432883287150003429802392229361583608686643243349727791976247247948618930423866180410558458272606627111270040091203073580238905303994472202930783207472394578498507764703191288249547659899997131166130259700604433891232298182348403175947450284433411265966789131024573629546048637848902243503970966798589660808533';
const y = '7046735122051745594868985795786176392951854019485729367165971776021501311096201521482383017242860186177215354508901537446984239682993203747271798136868016921883953390308299741287014686008274215001426444189972901892121945650333202105534018888882197552388434304153312708859768386971193915314738375008791798536164901595463713712574129466783480981077498017586306273866594394401039338841105927980179401433149438028686338492134818995843560711439253445043076178166622915392760675509176356257990398772342230639242314592068285808565623831103115873314006496120730338309413064358649726464219249576117734308027594482849210379533';

const setup = `
  var pk = new ElGamal.PublicKey(new BigInt('${p}',10), new BigInt('${q}',10),
                                 new BigInt('${g}',10), new BigInt('${y}',10));
  var pts = [new ElGamal.Plaintext(BigInt.ONE, pk, false),
             new ElGamal.Plaintext(pk.g, pk, false)];
  function encryptBallot(n) {
    var cts = [], proofs = [];
    for (var i = 0; i < n; i++) {
      var m = Math.random() < 0.5 ? 0 : 1;
      var r = Random.getRandomInteger(pk.q);
      var ct = ElGamal.encrypt(pk, pts[m], r);
      var proof = ct.generateDisjunctiveProof(pts, m, r, ElGamal.disjunctive_challenge_generator);
      cts.push(ct); proofs.push(proof);
    }
    return [cts, proofs];
  }
  function verifyBallot(cts, proofs) {
    var ok = true;
    for (var i = 0; i < cts.length; i++)
      ok = ok && cts[i].verifyDisjunctiveProof(pts, proofs[i], ElGamal.disjunctive_challenge_generator);
    return ok;
  }
`;
vm.runInContext(setup, ctx);

const n = parseInt(process.argv[2] || '7', 10);
const iters = parseInt(process.argv[3] || '30', 10);

// warm-up
vm.runInContext('encryptBallot(' + n + ')', ctx);

const encT = [], verT = [];
let allOk = true;
for (let i = 0; i < iters; i++) {
  let t0 = process.hrtime.bigint();
  const [cts, proofs] = vm.runInContext(`encryptBallot(${n})`, ctx);
  let t1 = process.hrtime.bigint();
  ctx.__cts = cts; ctx.__proofs = proofs;
  let t2 = process.hrtime.bigint();
  const ok = vm.runInContext('verifyBallot(__cts, __proofs)', ctx);
  let t3 = process.hrtime.bigint();
  allOk = allOk && ok;
  encT.push(Number(t1 - t0) / 1e6);
  verT.push(Number(t3 - t2) / 1e6);
}
const median = (a) => { const s = [...a].sort((x, y) => x - y); const l = s.length;
  return l % 2 ? s[(l - 1) / 2] : (s[l / 2 - 1] + s[l / 2]) / 2; };
const mean = (a) => a.reduce((x, y) => x + y, 0) / a.length;

console.log(`Helios booth JS (jsbn), n=${n}, iters=${iters}, all verified=${allOk}`);
console.log(`ballot encryption + proofs: median ${median(encT).toFixed(2)} ms, mean ${mean(encT).toFixed(2)} ms`);
console.log(`ballot verification:        median ${median(verT).toFixed(2)} ms, mean ${mean(verT).toFixed(2)} ms`);
