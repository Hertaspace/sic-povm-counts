#!/usr/bin/env python3
"""Independent d5/p3 cell audit: coefficients, identities, cells, final UNSAT.

Replays 15 old +43 branch-fixed new minimal-support certificates and the
large-support certificate, without CAS. Verifies cut formulas against their
minimum-term metadata by Z3 CLI, then replays manifest-ordered final SMT.
Only e90_* files are written; all subprocesses have explicit short limits.
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
import hashlib
import json
import re
import subprocess
import time
from e90_support_audit import make_matrices,structure_constants,minor_polynomials,square_polynomials
from e90_initial_audit import Polynomial,parse_polynomial,local_context,target_initial_function

H=Path(__file__).resolve().parent

def main():
    started=time.monotonic();d=5;p=3;n=25
    E,F,root,lead=local_context(d,p);mats=make_matrices(d,E,E.reduce([0,1]))
    constants=structure_constants(d,E,E.reduce([0,1]),mats)
    independent=minor_polynomials(d,E,mats,True)+square_polynomials(d,E,constants,True)[1:]
    rows=json.loads((H/'e04_weighted_screen.json').read_text())['results']
    row=next(r for r in rows if (r['d'],r['p'],r['representative_mask'])==(5,3,992))
    target_raw,target_lead=target_initial_function()(row,return_polynomials=True)
    assert len(independent)==len(target_raw)==124
    for left,right in zip(independent,target_raw):
        assert left=={k:v for k,v in right.items() if any(v)}
        for coefficient in left.values():assert target_lead(coefficient)==lead(coefficient)
    # Keep target insertion order only to interpret saved term indices; every
    # coefficient and monomial has just been matched to independent matrices.
    ordered=[[(mon,*lead(c)) for mon,c in poly.items() if any(c)] for poly in target_raw]
    for poly in ordered:assert poly
    cached=[[(mon,*lead(c)) for mon,c in poly.items()] for poly in independent]
    one=Polynomial(F,{():F.one})
    def const(c):return Polynomial(F,{():c}) if any(c) else Polynomial(F)
    variables={s:Polynomial(F,{(s,):F.one}) for s in ['y','t']+[f'z{q}' for q in range(n)]}
    def expected_initials(weights,mask,fixed):
        first=min(q for q in range(1,n) if mask>>q&1)
        z=lambda q:one if q==first else variables[f'z{q}']
        out=[]
        for poly in cached:
            vals=[v+sum(weights[q] for q in mon) for mon,v,c in poly];low=min(vals)
            g=Polynomial(F)
            for (mon,v,c),value in zip(poly,vals):
                if value==low:g=g+const(c)*z(mon[0])*z(mon[1])
            out.append(g)
        seen=set()
        for q in range(1,n):
            if q in seen:continue
            u,v=divmod(q,d);s=(-u%d)*d+(-v%d);seen.update([q,s])
            _,c=constants[q,s];value,coefficient=lead(c);assert value==0
            out.append(const(coefficient)*z(q)*z(s)-variables['t'])
        out += [variables['z0']**2-2*variables['t'],variables['t']*variables['y']-1]
        if fixed:
            assert mask==992 and first==5
            tau=F.reduce([0,1])
            out += [variables[f'z{5+v}']-const(F.power(tau,v)) for v in range(1,5)]
        return out
    def term_smt(mon,value):return '(+ '+' '.join([f'w{q}' for q in mon]+[str(value)])+')'
    # A common weight domain. Legacy cuts use w_q; optimized cuts use mu,u_q.
    unknown=[1,2,10,11,12,13,14]
    smt=['(set-logic QF_LRA)','(declare-const mu Real)']
    smt += [f'(declare-const w{q} Real)' for q in range(n)]
    smt += [f'(declare-const u{q} Real)' for q in unknown]
    smt += ['(assert (> mu 0))','(assert (= w0 (+ 1 (/ mu 2))))']
    for q in range(1,n):
        u,v=divmod(q,d);s=(-u%d)*d+(-v%d)
        if 5<=q<=9:expr='0'
        elif 20<=q<=24:expr='mu'
        elif q in unknown:expr=f'u{q}'
        else:assert s in unknown;expr=f'(- mu u{s})'
        smt.append(f'(assert (= w{q} {expr}))')
    for q in unknown:smt.append(f'(assert (and (> u{q} 0) (< u{q} mu)))')
    cut_paths=sorted(H.glob('e08_d5_p3_m992_c??_cut.json'))+sorted(H.glob('e08b_d5_p3_m992_c??_cut.json'))
    assert len(cut_paths)==58
    cut_paths += sorted(H.glob('e08_d5_p3_m32736_c??_cut.json'))
    assert len(cut_paths)==59
    records=[]
    for path in cut_paths:
        cut=json.loads(path.read_text());fixed=path.name.startswith('e08b_');mask=32736 if '_m32736_' in path.name else 992
        weights=list(map(Fraction,cut['weights']));mu=Fraction(cut['mu'])
        assert 2*weights[0]==2+mu and mu>0
        for q in range(1,n):
            u,v=divmod(q,d);s=(-u%d)*d+(-v%d)
            assert weights[q]+weights[s]==mu
            assert (weights[q]==0)==bool(mask>>q&1)
            assert weights[q]>=0
        replay_name=path.name.replace('_cut.json','_replay.sing');source=(H/replay_name).read_text()
        texts=re.search(r'ideal I=(.*?);\n',source,re.S)[1].split(',')
        actual=[parse_polynomial(g,F,n) for g in texts]
        assert actual==expected_initials(weights,mask,fixed),path.name
        multiplier_text=re.findall(r'Verify=Verify\+\((.*?)\)\*I\[(\d+)\];',source,re.S)
        indices=[int(i) for _,i in multiplier_text]
        assert indices==cut['nonzero_lift_generator_indices_one_based'],path.name
        total=Polynomial(F)
        for value,index in multiplier_text:total=total+parse_polynomial(value.replace('\n',' '),F,n)*actual[int(index)-1]
        assert total==1,path.name
        original=sorted({i-1 for i in indices if i<=len(ordered)})
        assert original==cut['original_polynomial_core_zero_based']
        assert original==[item['polynomial_index_zero_based'] for item in cut['cell']]
        conditions=[]
        for item in cut['cell']:
            index=item['polynomial_index_zero_based'];terms=ordered[index]
            values=[v+sum(weights[q] for q in mon) for mon,v,c in terms];low=min(values)
            leaders=[j for j,value in enumerate(values) if value==low]
            assert leaders==item['leader_term_indices_zero_based'],path.name
            mon,value,_=terms[leaders[0]];reference=term_smt(mon,value)
            for j,(mon,value,_) in enumerate(terms):
                op='=' if j in leaders else '>'
                conditions.append(f'({op} {term_smt(mon,value)} {reference})')
        if mask==992:
            actual_cut=re.fullmatch(r'\(assert\s+([\s\S]*)\)',cut['cut_smt2'])[1]
            expected_cut='(not (and '+' '.join(conditions)+'))'
            smt += ['(push 1)',f'(assert (xor {actual_cut} {expected_cut}))','(check-sat)','(pop 1)']
        record=dict(cut=path.name,replay=replay_name,fixed_minimal_point=fixed,identity='exactly 1',
                    generators=len(actual),multipliers=len(indices),core_polynomials=len(original),
                    cell_leaders='exact match',replay_sha256=hashlib.sha256(source.encode()).hexdigest())
        records.append(record)
        if len(records)%10==0:print('verified identities and cells',len(records),flush=True)
    equivalence_payload='\n'.join(smt)+'\n'
    eq=subprocess.run(['z3','-T:10','memory_max_size=2048','-in'],input=equivalence_payload,
                      text=True,capture_output=True,timeout=11)
    assert eq.returncode==0 and eq.stdout.split()==['unsat']*58,(eq.returncode,eq.stdout,eq.stderr)
    (H/'e90_d5_cut_equivalence.out').write_text(eq.stdout+eq.stderr)
    # Use the explicit final_smt_files manifest, never the stale unsplit path.
    manifest=json.loads((H/'e08b_optimized_cells.json').read_text())
    final=next(r for r in manifest['results'] if r['d']==5)
    assert final['status']=='covered_UNSAT' and final['cut_count']==43
    names=final['final_smt_files'];assert names==sorted(names) and len(names)==5
    payload=''.join((H/name).read_text() for name in names)
    result=subprocess.run(['z3','-T:5','memory_max_size=2048','-in'],input=payload,
                          text=True,capture_output=True,timeout=6)
    assert result.returncode==0 and result.stdout.strip()=='unsat',(result.returncode,result.stdout,result.stderr)
    (H/'e90_d5_final_smt.out').write_text(result.stdout+result.stderr)
    # The large support has a separate one-cell complete cover.
    large=json.loads((H/'e08_d5_p3_m32736_summary.json').read_text())
    assert large['status']=='covered_UNSAT'
    large_payload=''.join((H/name).read_text() for name in large['final_smt_files'])
    result_large=subprocess.run(['z3','-T:5','memory_max_size=2048','-in'],input=large_payload,
                                text=True,capture_output=True,timeout=6)
    assert result_large.returncode==0 and result_large.stdout.strip()=='unsat'
    (H/'e90_d5_large_final_smt.out').write_text(result_large.stdout+result_large.stderr)
    report=dict(d=5,p=3,old_minimal_cut_identities=15,new_minimal_cut_identities=43,
                large_support_cut_identities=1,cut_formula_equivalence_checks=58,records=records,
                minimal_final_smt_files=[dict(name=name,bytes=(H/name).stat().st_size,
                    sha256=hashlib.sha256((H/name).read_bytes()).hexdigest()) for name in names],
                minimal_final_sha256=hashlib.sha256(payload.encode()).hexdigest(),minimal_final='unsat',
                large_final_sha256=hashlib.sha256(large_payload.encode()).hexdigest(),large_final='unsat',
                z3_version=subprocess.check_output(['z3','-version'],text=True).strip(),
                elapsed_seconds=round(time.monotonic()-started,6))
    (H/'e90_d5_cells_audit.json').write_text(json.dumps(report,indent=2)+'\n')
    message='ALL_CHECKS_PASS: 59 polynomial identities; 58 exact cell-formula equivalences; both d5p3 support types UNSAT; seconds='+str(report['elapsed_seconds'])
    (H/'e90_d5_cells_audit.out').write_text(message+'\n');print(message,flush=True)

if __name__=='__main__':main()
