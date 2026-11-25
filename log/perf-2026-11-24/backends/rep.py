import sys,time,subprocess,resource,statistics as st,os
# rep.py N timeout cmd...   one warm-up (N>1) then N runs
n=int(sys.argv[1]); to=float(sys.argv[2]); cmd=sys.argv[3:]; W=[];U=[];M=[]; outs=set()
for i in range(n+(1 if n>1 else 0)):
    t=time.perf_counter(); pid=subprocess.Popen(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    try: o,_=pid.communicate(timeout=to)
    except subprocess.TimeoutExpired: pid.kill(); pid.communicate(); print('TIMEOUT',to,cmd); sys.exit()
    w=time.perf_counter()-t
    if i or n==1: W.append(w)
    outs.add((pid.returncode,o.decode(errors='replace')[:60].strip()))
u=resource.getrusage(resource.RUSAGE_CHILDREN)
print('%s runs=%d wall median %.3f min %.3f max %.3f s; peak RSS %.1f MB; out %s'%(' '.join(cmd)[-60:],n,st.median(W),min(W),max(W),u.ru_maxrss/2**20,outs))
