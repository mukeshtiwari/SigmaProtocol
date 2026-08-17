const fs = require('fs');
const file = process.argv[2];
const iters = parseInt(process.argv[3] || '10', 10);
const median = a => { const s=[...a].sort((x,y)=>x-y); const l=s.length;
  return l%2 ? s[(l-1)/2] : (s[l/2-1]+s[l/2])/2; };
(async () => {
  const mod = await WebAssembly.compile(fs.readFileSync(file));
  const times = [];
  for (let i = 0; i < iters; i++) {
    const inst = await WebAssembly.instantiate(mod, { env: {} });
    const t0 = process.hrtime.bigint();
    inst.exports.main_function();
    const t1 = process.hrtime.bigint();
    if (inst.exports.out_of_mem && inst.exports.out_of_mem.value === 1) {
      console.log('OUT OF MEMORY on iteration', i); process.exit(1);
    }
    times.push(Number(t1 - t0) / 1e6);
    if (i === 0) console.log('  mem used:', (inst.exports.mem_ptr.value/1048576).toFixed(1), 'MB');
  }
  console.log(`${file}: iters=${iters} median ${median(times).toFixed(2)} ms, ` +
              `min ${Math.min(...times).toFixed(2)} ms, max ${Math.max(...times).toFixed(2)} ms`);
})().catch(e => { console.error('ERR', e); process.exit(1); });
