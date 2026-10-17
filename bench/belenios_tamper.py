#!/usr/bin/env python3
"""Tamper with a Belenios 3.x election archive on Ed25519, for testing the
certified verifier. Produces archives in which one ballot has an invalid
proof but a valid signature (re-signed with the voter's private
credential), or a wrong decryption factor, result or credential weight.

usage: belenios_tamper.py ARCHIVE.bel PRIVATE_CREDS.txt OUTDIR

Run the verifier on the outputs with BELENIOS_SKIP_HASH_CHECK=1, since
the archive's content hashes no longer match (a real verifier rejects the
archive for that reason alone; the switch lets the tampered data reach
the certified core)."""
import json, os, sys, tarfile, hashlib, base64, secrets, shutil, tempfile
# Independent check of Belenios 3.2.0 ballot proofs on Ed25519 (pure Python).
import json, glob, os, hashlib, sys
p = 2**255 - 19
l = 2**252 + 27742317777372353535851937790883648493
d = (-121665 * pow(121666, p-2, p)) % p
a = p - 1
def add(P, Q):
    x1,y1=P; x2,y2=Q
    x3=(x1*y2+x2*y1)*pow(1+d*x1*x2*y1*y2,p-2,p)%p
    y3=(y1*y2-a*x1*x2)*pow(1-d*x1*x2*y1*y2,p-2,p)%p
    return (x3,y3)
def mul(k,P):
    R=(0,1)
    while k:
        if k&1: R=add(R,P)
        P=add(P,P); k>>=1
    return R
def neg(P): return ((-P[0])%p, P[1])
def modsqrt(x2):
    v=pow(2*x2, (p-5)//8, p); i=(2*x2*v*v)%p; return (x2*v*(i-1))%p
def uncompress(z):
    y=z & ((1<<255)-1); sign=z>>255
    y2=y*y%p; x2=(y2-1)*pow(d*y2+1,p-2,p)%p
    x=modsqrt(x2)
    assert x*x%p==x2, "not on curve"
    if (x&1)!=sign: x=p-x
    return (x,y)
def compress(P):
    x,y=P; return y | ((x&1)<<255)
def tostr(P): return '%064x' % compress(P)
def ofstr(s): return uncompress(int(s,16))
def hashq(prefix, pts):
    msg = prefix + ','.join(tostr(P) for P in pts)
    return int(hashlib.sha256(msg.encode()).hexdigest(),16) % l
B=(15112221349535400772501151409588531511454012693041857206046113283949847762202,
   46316835694926478169428394003475163141307993866256225615783033603165251855960)
g=B

def main():
    archive, creds_file, outdir = sys.argv[1:4]
    os.makedirs(outdir, exist_ok=True)
    with tarfile.open(archive) as t:
        names=t.getnames(); files={n: t.extractfile(n).read() for n in names}
    def js(n): return json.loads(files[n].decode())
    events=[n for n in names if n.endswith('.event.json')]
    def payloads(kind): return [js(e)['payload']+'.data.json' for e in events if js(e)['type']==kind]
    setup=js(payloads('Setup')[0]); election=js(setup['election']+'.data.json'); uuid=election['uuid']
    ballots=payloads('Ballot'); tally=js(payloads('EncryptedTally')[0])
    pds=[js(js(p)['payload']+'.data.json') for p in payloads('PartialDecryption')]; pdfiles=[js(p)['payload']+'.data.json' for p in payloads('PartialDecryption')]
    result=payloads('Result')[0]; creds=setup['credentials']+'.data.json'
    secrets_={}
    for line in open(creds_file):
        parts=line.split()
        if len(parts)>=2:
            c=parts[1]; xs=''.join(hashlib.sha256(('derive_credential|%s|%d|%s'%(uuid,i,c)).encode()).hexdigest() for i in (0,1))
            secrets_[tostr(mul(int(xs,16)%l, g))]=int(xs,16)%l
    def resign(b):
        s=secrets_[b['credential']]
        bws=dict(b); bws.pop('signature'); raw=json.dumps(bws, separators=(',',':'))
        h=base64.b64encode(hashlib.sha256(raw.encode()).digest()).decode().rstrip('=')
        w=secrets.randbelow(l); A=mul(w,g); ch=hashq('sig|'+h+'|',[A]); rs=(w - s*ch) % l
        b['signature']={'hash':h,'proof':{'challenge':str(ch),'response':str(rs)}}
    def write(name, changed):
        out=os.path.join(outdir, name+'.bel')
        with tarfile.open(out,'w') as t:
            for n in names:
                data=changed.get(n, files[n]); info=tarfile.TarInfo(n); info.size=len(data)
                import io; t.addfile(info, io.BytesIO(data))
        print(out)
    inc=lambda x: str((int(x)+1)%l)
    b0=ballots[0]
    def ballot_variant(name, edit):
        b=js(b0); edit(b); resign(b); write(name, {b0: json.dumps(b, separators=(',',':')).encode()})
    ballot_variant('indiv', lambda b: b['answers'][0]['individual_proofs'][0][0].__setitem__('response', inc(b['answers'][0]['individual_proofs'][0][0]['response'])))
    ballot_variant('overall', lambda b: b['answers'][0]['overall_proof'][0].__setitem__('response', inc(b['answers'][0]['overall_proof'][0]['response'])))
    for i,a in enumerate(js(b0)['answers']):
        if a.get('blank_proof'):
            ballot_variant('blank', lambda b: b['answers'][i]['blank_proof'][0].__setitem__('response', inc(b['answers'][i]['blank_proof'][0]['response'])))
            break
    pd=dict(pds[0]); pd['decryption_factors'][0][0]=pd['decryption_factors'][0][1] if len(pd['decryption_factors'][0])>1 else pd['decryption_factors'][1][0]
    write('factor', {pdfiles[0]: json.dumps(pd, separators=(',',':')).encode()})
    r=js(result); v=r['result'][0][0]; r['result'][0][0]= (str(int(v)+1) if isinstance(v,str) else v+1)
    write('result', {result: json.dumps(r, separators=(',',':')).encode()})
    cl=js(creds)
    if ',' in cl[0]:
        pk,w=cl[0].split(','); cl[0]=pk+','+str(int(w)+1); write('weight', {creds: json.dumps(cl, separators=(',',':')).encode()})
if __name__=='__main__': main()
