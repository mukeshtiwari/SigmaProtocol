import re,statistics as st
L='log/perf-2026-11-24/'
r=lambda f:open(L+f).read()
s1=lambda t:(f"{t:.2f}" if t<1 else f"{t:.1f}" if t<10 else f"{t:.0f}")+"\\,s"
mn=lambda t:(f"{t/60:.1f}" if t<600 else f"{t/60:.0f}")+"\\,min"
for m in (3,5,7,10,13,17):
    a=r(f'first-{m}.log');b=r(f'simple-{m}.log')
    g=lambda p,x:float(re.search(p,x).group(1))
    print('ballot',m,s1(g(r'NIZK proofs: median ([\d.]+)',a)),s1(g(r'verification: +median ([\d.]+)',a)),g(r', ([\d.]+) KB',a),'|',g(r'prover pass\): median ([\d.]+)',b),g(r'verification: +median ([\d.]+)',b),g(r', ([\d.]+) KB',b))
first_lo=[];
for e in '201106 201206 201306 201406 201506 201606 201706 201806 201906 202006 202106 202206 202306'.split():
    enc=st.median(map(float,re.findall(r'proved in ([\d.]+) s',r(f'encrypt-council-{e}.log'))))
    M=r(f'main-council-{e}.log'); G=r(f'gentoo3-council-{e}-ballots.log')
    m,N=re.search(r'm = (\d+) candidates, N = (\d+)',M).groups()
    v=float(re.search(r'verify median ([\d.]+)',M).group(1))
    benc=float(re.search(r'median ([\d.]+) s per ballot',G).group(1)); bv=float(re.search(r'verify median ([\d.]+)',G).group(1))
    cg,cv=map(int,re.search(r'generation (\d+) s, verification (\d+) s',M).groups())
    print(f"    {e[:4]} & {m} & {N} & {enc:.1f}/{v:.1f} | {benc:.1f}/{bv:.1f} | {cg} {cv} => {mn(cg)} {mn(cv)}")
