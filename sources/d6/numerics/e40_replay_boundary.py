#!/usr/bin/env python3.14
"""Replay every d6/p7 source identity and rebuild all six weight covers.

No historical script main is executed and no historical file is written.
The 147 identities are checked in exact sparse F49 arithmetic. A fresh
QF_LRA solver is built from the original necessary equations and certified
leader cells only; e31 and stored final SMT assertions are never loaded.
"""

# Locate dependencies relative to the public repository root.
from pathlib import Path as _EvidencePath
import sys as _evidence_sys
_evidence_sys.dont_write_bytecode = True
if not __debug__:
    raise RuntimeError("Python optimization disables certificate assertions")
_evidence_root = next(p for p in _EvidencePath(__file__).resolve().parents
                      if (p / "replay" / "portable.py").is_file())
_evidence_sys.path.insert(0, str(_evidence_root / "replay"))
from portable import public_root, executable, resident_bytes
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from fractions import Fraction
from collections import Counter
from functools import lru_cache
import argparse,gzip,hashlib,importlib.util,json,re,time
import z3

H=Path(__file__).resolve().parent
OLD=public_root(__file__)/'sources/escape/numerics'
sys.path.insert(0,str(OLD))
import e90_initial_audit as A
import e90_support_audit as S
MASKS=[4032,258048,352325568,704647104,262080,1056968640]
EXPECTED_COUNTS={4032:81,258048:52,352325568:3,704647104:7,262080:3,1056968640:1}
BLOCK=['z8-5','z10-4','z9-5*z7','z11-4*z7','z26-2*z24','z28-4*z24','z27-2*z25','z29-4*z25']


def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def unpack(root,manifest):
    data=gzip.decompress(b''.join((root/name).read_bytes() for name in manifest['files']))
    assert hashlib.sha256(data).hexdigest()==manifest['uncompressed_sha256']
    if 'uncompressed_bytes' in manifest:assert len(data)==manifest['uncompressed_bytes']
    return data
def parse(text,F):return A.Polynomial(F).coerce(A.parse_polynomial(text,F,36))
def opposite(q):r,k=divmod(q,6);return (-r%6)*6+(-k%6)


def context():
    E,F,root,lead=A.local_context(6,7)
    mats=S.make_matrices(6,E,E.reduce([0,1]))
    cc=S.structure_constants(6,E,E.reduce([0,1]),mats)
    independent=S.minor_polynomials(6,E,mats,True)+S.square_polynomials(6,E,cc,True)[1:]
    rows=json.loads((OLD/'e04_weighted_screen.json').read_text())['results']
    rows={r['representative_mask']:r for r in rows if (r['d'],r['p'])==(6,7)}
    target,target_lead=A.target_initial_function()(rows[4032],return_polynomials=True)
    assert len(target)==len(independent)==260
    coefficient_leads={}
    for left,right in zip(independent,target):
        assert left=={mon:c for mon,c in right.items() if any(c)}
        for c in left.values():
            if c not in coefficient_leads:
                coefficient_leads[c]=lead(c)
                assert coefficient_leads[c]==target_lead(c)
    ordered=[[(mon,*coefficient_leads[c]) for mon,c in poly.items() if any(c)] for poly in target]
    assert all(ordered)
    return F,tuple(x%7 for x in root),ordered,rows


def sources(mask):
    out=[]
    for pattern in [f'e08_d6_p7_m{mask}_c??_cut.json',f'e08b_d6_p7_m{mask}_c??_cut.json']:
        for path in sorted(OLD.glob(pattern)):
            cut=json.loads(path.read_text())
            replay=OLD/path.name.replace('_cut.json','_replay.sing')
            text=replay.read_text()
            gens=re.search(r'ideal I=(.*?);\n',text,re.S)[1].split(',')
            pairs=re.findall(r'Verify=Verify\+\((.*?)\)\*I\[(\d+)\];',text,re.S)
            assert pairs
            members=[dict(generator_index_zero_based=int(i)-1,generator=gens[int(i)-1],multiplier=m.replace('\n',' ')) for m,i in pairs]
            out.append(dict(file=str(path),cut=cut,members=members,all_generators=gens,
                            hashes={str(path):digest(path),str(replay):digest(replay)}))
    for path in sorted(OLD.glob(f'e08c_d6_p7_m{mask}_*c[0-9][0-9][0-9].json')):
        cut=json.loads(path.read_text())
        out.append(dict(file=str(path),cut=cut,members=cut['members'],hashes={str(path):digest(path)}))
    if mask==4032:
        summary=json.loads((H/'e10_p7_r1_plain.json').read_text())
        assert summary['uses_e31_strengthening'] is False
        manifests=summary['certificates']
    elif mask==1056968640:
        manifests=[json.loads((H/'e10_p7_component.json').read_text())['certificate']]
    else:manifests=[]
    for manifest in manifests:
        cut=json.loads(unpack(H,manifest))
        out.append(dict(file='+'.join(manifest['files']),cut=cut,members=cut['members'],
                        hashes={str(H/name):digest(H/name) for name in manifest['files']}))
    assert len(out)==EXPECTED_COUNTS[mask],(mask,len(out))
    return out


def replay_identity(record,mask,F,root,rows,ordered):
    cut=record['cut'];weights=list(map(Fraction,cut['weights']));mu=2*(weights[0]-1)
    Sset={q for q in range(1,36) if mask>>q&1}
    assert mu>0 and all(weights[q]+weights[opposite(q)]==mu for q in range(1,36))
    assert {q for q in range(1,36) if weights[q]==0}==Sset
    assert all(weights[q]>=0 for q in range(36))
    row=dict(rows[mask],weights=weights,mu=mu)
    texts,FF,first,details=A.independent_initials(row)
    assert FF.f==F.f and FF.p==F.p and len(texts)==281
    minimal=mask in (4032,258048)
    if minimal:
        u=first//6
        texts += [f'z{q}-'+F.text(F.power(root,u*(q%6))) for q in sorted(Sset) if q!=first]
    if cut.get('residue_component_normalization'):
        assert mask==1056968640
        normalization=cut['residue_component_normalization']
        assert normalization['a_support']==[0,3] and normalization['b_support']==[2,5]
        assert [parse(g,F) for g in normalization['relations']]==[parse(g,F) for g in BLOCK]
        texts+=BLOCK
    expected=[parse(g,F) for g in texts]
    if 'all_generators' in record:
        assert [parse(g,F) for g in record['all_generators']]==expected
    total=A.Polynomial(F);indices=[]
    for member in record['members']:
        index=member['generator_index_zero_based']
        assert parse(member['generator'],F)==expected[index]
        multiplier=parse(member['multiplier'],F)
        assert multiplier.terms
        total=total+multiplier*expected[index];indices.append(index)
    assert total==1,record['file']
    assert len(indices)==len(set(indices))
    core=sorted({i for i in indices if i<260})
    assert core==[part['polynomial_index_zero_based'] for part in cut['cell']]
    for part in cut['cell']:
        ts=ordered[part['polynomial_index_zero_based']]
        values=[v+sum(weights[q] for q in mon) for mon,v,c in ts]
        assert [i for i,v in enumerate(values) if v==min(values)]==part['leader_term_indices_zero_based']
    return dict(file=record['file'],members=len(indices),identity='exactly 1',core_size=len(core),
                normalized_residue_point=minimal,residue_component=bool(cut.get('residue_component_normalization')),
                hashes=record['hashes'])


def fresh_cover(mask,records,ordered,timeout):
    Sset={q for q in range(1,36) if mask>>q&1};negative={opposite(q) for q in Sset}
    free=[q for q in range(1,36) if q not in Sset|negative and q<opposite(q)]
    mu=z3.Real(f'e40_mu_{mask}');xs=[mu]+[z3.Real(f'e40_x_{mask}_{q}') for q in free]
    dim=len(xs);vecs=[]
    for q in range(36):
        vec=[Fraction(0)]*(dim+1)
        if q==0:vec[0]=Fraction(1,2);vec[-1]=1
        elif q in Sset:pass
        elif q in negative:vec[0]=1
        elif q==opposite(q):vec[0]=Fraction(1,2)
        elif q in free:vec[1+free.index(q)]=1
        else:vec[0]=1;vec[1+free.index(opposite(q))]=-1
        vecs.append(tuple(vec))
    @lru_cache(None)
    def lin(vec):return z3.Sum([z3.RealVal(str(c))*x for c,x in zip(vec[:-1],xs) if c]+[z3.RealVal(str(vec[-1]))])
    def term_form(mon,val,perm=None):
        vec=[sum(vecs[q if perm is None else perm[q]][i] for q in mon) for i in range(dim+1)]
        vec[-1]+=val;return tuple(vec)
    solver=z3.Solver();solver.set(timeout=int(timeout*1000));solver.add(mu>0)
    for x in xs[1:]:solver.add(x>0,x<mu)
    for ts in ordered:
        forms=Counter(term_form(mon,val) for mon,val,c in ts)
        for form,count in forms.items():
            if count==1:solver.add(z3.Or(*[lin(other)<=lin(form) for other in forms if other!=form]))
    images=[]
    for sign in (1,-1):
        for c in range(6):
            perm=[r*6+(sign*k+c*r)%6 for r in range(6) for k in range(6)]
            assert {perm[q] for q in Sset}==Sset
            assert all(perm[opposite(q)]==opposite(perm[q]) for q in range(36))
            images.append(perm)
    for record in records:
        for perm in images:
            conditions=[]
            for part in record['cut']['cell']:
                ts=ordered[part['polynomial_index_zero_based']]
                leaders=set(part['leader_term_indices_zero_based'])
                forms=[term_form(mon,val,perm) for mon,val,c in ts]
                reference=lin(forms[min(leaders)])
                conditions += [lin(form)==reference if i in leaders else lin(form)>reference for i,form in enumerate(forms)]
            solver.add(z3.Not(z3.And(*conditions)))
    tick=time.monotonic();answer=solver.check();elapsed=time.monotonic()-tick
    result=dict(mask=mask,status=str(answer),source_identities=len(records),group_images_per_identity=12,
                free_pairs=len(free),seconds=round(elapsed,6),uses_e31=False,uses_saved_smt=False)
    if answer==z3.unknown:result['reason']=solver.reason_unknown()
    raw=solver.to_smt2().encode();comp=gzip.compress(raw,mtime=0);files=[]
    for i in range(0,len(comp),900000):
        name=f'e40_m{mask}_final.smt2.gz.part{i//900000:03d}'
        (H/name).write_bytes(comp[i:i+900000]);files.append(name)
    result['smt']=dict(files=files,uncompressed_bytes=len(raw),compressed_bytes=len(comp),sha256=hashlib.sha256(raw).hexdigest())
    assert answer==z3.unsat,result
    return result


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--members-only',action='store_true');ap.add_argument('--timeout',type=float,default=120)
    args=ap.parse_args();start=time.monotonic()
    z3.set_param('memory_max_size',12000);z3.set_param('smt.random_seed',20261031);z3.set_param('sat.random_seed',20261031)
    F,root,ordered,rows=context();replays=[];covers=[]
    for mask in MASKS:
        records=sources(mask)
        for record in records:replays.append(replay_identity(record,mask,F,root,rows,ordered))
        print(json.dumps(dict(mask=mask,identities=len(records),identity_replay='PASS')),flush=True)
        if not args.members_only:
            cover=fresh_cover(mask,records,ordered,args.timeout);covers.append(cover)
            print(json.dumps(cover),flush=True)
        out=dict(status='IN_PROGRESS',seed=20261031,identities=replays,covers=covers,seconds=round(time.monotonic()-start,6))
        (H/'e40_replay_boundary.json').write_text(json.dumps(out,indent=2)+'\n')
    assert len(replays)==147
    if not args.members_only:assert len(covers)==6 and all(r['status']=='unsat' for r in covers)
    out.update(status='PASS',identity_count=147,complete_boundary_coverage=not args.members_only,
               versions={'python':sys.version,'z3':z3.get_version_string()},
               source_hashes={str(path):digest(path) for path in [Path(__file__),OLD/'e05_initial_forms.py',OLD/'e90_initial_audit.py',OLD/'e90_support_audit.py']},
               seconds=round(time.monotonic()-start,6))
    encoded=json.dumps(out,indent=2)+'\n';assert len(encoded.encode())<2**20
    (H/'e40_replay_boundary.json').write_text(encoded)
    print('ALL_CHECKS_PASS',147,'source identities;',len(covers),'fresh UNSAT covers; seconds',out['seconds'],flush=True)


if __name__=='__main__':main()
