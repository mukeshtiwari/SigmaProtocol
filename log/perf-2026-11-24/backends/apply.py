import re
def sub(f,pairs):
    s=open(f).read()
    for a,b in pairs:
        assert s.count(a)==1,(f,a,s.count(a)); s=s.replace(a,b)
    open(f,'w').write(s)
E='sections/eval.tex'
sub(E,[
(r'59\,KB & 0.69\,s & 0.41\,s &',r'59\,KB & 0.18\,s & 0.11\,s &'),
(r'216\,KB & 2.9\,s & 1.6\,s & 22\,KB & 0.07\,s & 0.11\,s',r'216\,KB & 0.76\,s & 0.44\,s & 22\,KB & 0.05\,s & 0.11\,s'),
(r'531\,KB & 7.9\,s & 4.3\,s & 36\,KB & 0.12\,s',r'531\,KB & 2.0\,s & 1.1\,s & 36\,KB & 0.10\,s'),
(r'1.4\,MB & 21.9\,s & 11.9\,s & 67\,KB & 0.25\,s',r'1.4\,MB & 5.6\,s & 3.0\,s & 67\,KB & 0.19\,s'),
(r'2.9\,MB & 59\,s & 31\,s & 108\,KB & 0.41\,s & 0.81\,s',r'2.9\,MB & 12\,s & 6.4\,s & 108\,KB & 0.32\,s & 0.80\,s'),
(r'6.2\,MB & 130\,s & 68\,s & 180\,KB & 0.71\,s',r'6.2\,MB & 26\,s & 14\,s & 180\,KB & 0.56\,s'),
(r'$180$ times faster',r'$47$ times faster'),(r'about $40$ times faster',r'about $9$ times faster'),
(r'about $5$\,ms',r'about $1.5$\,ms'),
('The extracted verifier accepted the three smallest of these\ncertificates; we did not run it on the other two.','The extracted verifier accepted all five of these certificates.'),
(r'5 & 64 & 11\,s & 14\,MB',r'5 & 64 & 2.8\,s & 14\,MB'),
(r'10 & 64 & 68\,s & 93\,MB',r'10 & 64 & 19\,s & 91\,MB'),
(r'20 & 64 & 8.0\,min',r'20 & 64 & 2.3\,min'),
(r'5 & 1024 & 2.8\,min & 0.21\,GB',r'5 & 1024 & 52\,s & 0.21\,GB'),
(r'10 & 1024 & 18.9\,min & 1.42\,GB',r'10 & 1024 & 5.7\,min & 1.40\,GB'),
('takes $26$--$132$\\,s and verifying $12$--$57$\\,s','takes $5.6$--$27$\\,s and verifying $3.0$--$14$\\,s'),
('$0.8$--$2.9$\\,s and verifies in $0.5$--$1.6$\\,s','$0.6$--$2.3$\\,s and verifies in $0.4$--$1.6$\\,s'),
('$18$ minutes at','$4.8$ minutes at'),('$144$ minutes','$41$ minutes'),
])
import importlib.util,subprocess
L='log/perf-2026-11-24/'
import statistics as st
r=lambda f:open(L+f).read()
sec=lambda t:(f"{t:.1f}" if t<10 else f"{t:.0f}")+r"\,s"
mn=lambda t:(f"{t/60:.1f}" if t<600 else f"{t/60:.0f}")+r"\,min"
s=open(E).read()
for e in '201106 201206 201306 201406 201506 201606 201706 201806 201906 202006 202106 202206 202306'.split():
    enc=st.median(map(float,re.findall(r'proved in ([\d.]+) s',r(f'encrypt-council-{e}.log'))))
    M=r(f'main-council-{e}.log'); G=r(f'gentoo3-council-{e}-ballots.log')
    m,N=re.search(r'm = (\d+) candidates, N = (\d+)',M).groups()
    v=float(re.search(r'verify median ([\d.]+)',M).group(1))
    be=float(re.search(r'median ([\d.]+) s per ballot',G).group(1)); bv=float(re.search(r'verify median ([\d.]+)',G).group(1))
    cg,cv=map(int,re.search(r'generation (\d+) s, verification (\d+) s',M).groups())
    new=f"    {e[:4]} & {m} & {N} & {sec(enc)} & {sec(v)} & {sec(be)} & {sec(bv)} & {mn(cg)} & {mn(cv)} \\\\"
    s,n=re.subn(rf"^    {e[:4]} & {m} & {N} &.*$",lambda _:new,s,flags=re.M); assert n==1,e
open(E,'w').write(s)
sub('sections/cortier.tex',[
(r'5 & 64 & 11\,s',r'5 & 64 & 2.8\,s'),(r'10 & 64 & 68\,s & 93\,MB',r'10 & 64 & 19\,s & 91\,MB'),
(r'20 & 64 & 8.0\,min',r'20 & 64 & 2.3\,min'),(r'5 & 1024 & 2.8\,min',r'5 & 1024 & 52\,s'),
(r'10 & 1024 & 18.9\,min & 1.42\,GB',r'10 & 1024 & 5.7\,min & 1.40\,GB'),
('between a tenth and three tenths of their\ntime','between a fortieth and a tenth of their\ntime'),
])
TAB=r'''
\begin{table}[h]
  \caption{One fixed seven-candidate approval ballot (not a Schulze
  ballot) through five back ends, on the machine of
  Section~\ref{sec:eval}. Moduli in bits. Medians of five runs (CakeML's
  ballot: one run; OCaml: random ballots, five runs of 30). C and wasm64
  include process start-up. Peregrine \texttt{13c701b} without its LLVM
  back end, CertiRocq 0.9.1, CakeML v3479, emscripten 7.0.1, Node 26.13.1.
  For performance only: primality is admitted in all rows but OCaml and
  Ed25519, and the CertiRocq-Wasm and CakeML code is compiled from a Rocq
  9.1 copy with three proofs also admitted. OOM: exceeds the linear
  memory.}
  \label{tab:backends}
  \centering\scriptsize\setlength{\tabcolsep}{3pt}
  \begin{tabular}{@{}lllrr@{}}
    \toprule
    back end & group & computation & time & memory \\
    \midrule
    OCaml, GMP & 2048 & prove & 37\,ms & \\
    & 2048 & verify & 20\,ms & \\
    C, GMP & 2048 & prove and verify & 44\,ms & 4\,MB \\
    & Ed25519 & prove and verify & 46\,ms & 4\,MB \\
    wasm64, mini-gmp & 2048 & prove and verify & 0.27\,s & 54\,MB \\
    & Ed25519 & prove and verify & 0.19\,s & 96\,MB \\
    CertiRocq-Wasm & 64 & prove & 0.26\,s & 137\,MB \\
    & 64 & prove and verify & 0.69\,s & 286\,MB \\
    & 128 & prove & 6.3\,s & 1150\,MB \\
    & 128 & prove and verify & OOM & \\
    & 256 & one vote & 8.2\,s & 1269\,MB \\
    & 256 & prove & OOM & \\
    & 2048 & $g^{65537}$ & 4.0\,s & 839\,MB \\
    & 2048 & prove & OOM & \\
    CakeML & 2048 & $g^{65537}$ & 1.1\,s & 1683\,MB \\
    & 2048 & prove & 24\,min & 6003\,MB \\
    \bottomrule
  \end{tabular}
\end{table}
'''
f='sections/extensions.tex'
sub(f,[
(r'5.2\,s & 2.6\,s',r'1.3\,s & 0.68\,s'),(r'17\,s & 8.7\,s',r'4.6\,s & 2.3\,s'),
(r'5 & 50 & 40{,}848 & 11.2\,MB & 163\,s & 83\,s',r'5 & 50 & 39{,}114 & 10.7\,MB & 43\,s & 21\,s'),
(r'7 & 100 & 190{,}376 & 52.3\,MB & 1{,}668\,s & 382\,s',r'7 & 100 & 194{,}618 & 53.5\,MB & 216\,s & 107\,s'),
])
s=open(f).read(); i=s.index(r'\label{tab:tallycost}'); j=s.index(r'\end{table}',i)+len(r'\end{table}')+1
open(f,'w').write(s[:j]+TAB+s[j:])
sub('sections/intro.tex',[('$2.4$ hours\n  (verification $71$ minutes)','$41$ minutes\n  (verification $21$ minutes)'),('in $68$ seconds','in $19$ seconds'),('in $19$ minutes.','in $5.7$ minutes.')])
print('applied')
