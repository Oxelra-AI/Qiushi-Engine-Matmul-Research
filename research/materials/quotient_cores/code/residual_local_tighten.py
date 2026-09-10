#!/usr/bin/env python3
"""analysis: branch-sensitive residual local tightening for quotient-support rows.

For a fixed corrected quotient branch, some points P are forced and some points
are forbidden.  For a candidate parent row U, compute the exact maximum number
of selected points that can lie in U among the remaining domain, subject to all
row inequalities crossing U with residual capacity c(W)-|P∩W|.

This implements the point that live search states carry more
information than unconditional child-subspace capacities.  The exported rows are
branch-conditional: a row U with tightened total cap p_U+M is valid only under
the specified branch force/forbid assumptions.  They must not be reused as
unconditional quotient Wang rows.
"""
from __future__ import annotations
import argparse, hashlib, itertools, json, struct, time
from collections import Counter
from pathlib import Path

ROOT = Path('research/research_record')
SPECS = ROOT/'workspace/data/quotient_branches/corrected_branch_specs.json'
MAGIC=b'E11WANG1'; REC='<BBHQQQQ'; RECSZ=struct.calcsize(REC)

def sha(path: Path) -> str:
    h=hashlib.sha256()
    with path.open('rb') as f:
        for c in iter(lambda: f.read(1<<20), b''):
            h.update(c)
    return h.hexdigest()

def load_rows(path: Path):
    d=path.read_bytes()
    if d[:8] != MAGIC:
        raise ValueError(f'{path}: bad magic {d[:8]!r}')
    n=struct.unpack('<I', d[8:12])[0]
    if len(d) != 12 + n*RECSZ:
        raise ValueError(f'{path}: size mismatch {len(d)} vs {12+n*RECSZ}')
    rows=[]; hist=Counter(); dimhist=Counter()
    for idx in range(n):
        off=12+idx*RECSZ
        cap,dim,pad,w0,w1,w2,w3=struct.unpack_from(REC,d,off)
        mask=int(w0)|(int(w1)<<64)|(int(w2)<<128)|(int(w3)<<192)
        rec=d[off:off+RECSZ]
        rows.append({'idx':idx,'cap':int(cap),'dim':int(dim),'mask':mask,'popcount':mask.bit_count(),'rec':rec})
        hist[int(cap)]+=1; dimhist[int(dim)]+=1
    return rows, {'path':str(path),'sha256':sha(path),'count':n,'cap_hist':{str(k):int(v) for k,v in sorted(hist.items())},'dim_hist':{str(k):int(v) for k,v in sorted(dimhist.items())}}

def pack_row(cap:int, dim:int, mask:int) -> bytes:
    return struct.pack(REC, int(cap), int(dim), 0, mask & ((1<<64)-1), (mask>>64)&((1<<64)-1), (mask>>128)&((1<<64)-1), (mask>>192)&((1<<64)-1))

def write_rows(path:Path, recs:list[bytes]):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('wb') as f:
        f.write(MAGIC); f.write(struct.pack('<I', len(recs)))
        for r in recs: f.write(r)

def bit_positions(mask:int):
    while mask:
        lsb=mask & -mask
        yield lsb.bit_length()-1
        mask ^= lsb

def point_mask(points):
    m=0
    for p in points:
        m |= 1<<int(p)
    return m

def choose_candidate_indices(mining_paths, rows, max_rows:int, allowed_caps:set[int]):
    score=Counter(); first={}
    for mp in mining_paths:
        j=json.loads(mp.read_text())
        for rr,rec in enumerate(j.get('rounds', [])):
            for pos,idx in enumerate(rec.get('violation_rows', [])):
                idx=int(idx); score[idx]+=1; first.setdefault(idx,(str(mp),rr,pos))
    if not score:
        return []
    cand=[]
    for idx,cnt in score.items():
        if idx < 0 or idx >= len(rows):
            continue
        r=rows[idx]
        if r['cap'] not in allowed_caps:
            continue
        cand.append((idx,cnt,r['cap'],r['dim'],r['popcount'],first[idx]))
    cand.sort(key=lambda t:(-t[1], t[2], t[3], -t[4], t[5][1], t[5][2], t[0]))
    return [x[0] for x in cand[:max_rows]]

def build_local_constraints(rows, U, force_mask:int, forbid_mask:int):
    pU=(U['mask'] & force_mask).bit_count()
    future_global=[p for p in bit_positions(U['mask']) if not ((force_mask|forbid_mask)>>p)&1]
    pos={p:i for i,p in enumerate(future_global)}
    n=len(future_global)
    best={}  # local intersection mask -> min residual cap
    infeas=False
    for W in rows:
        pW=(W['mask'] & force_mask).bit_count()
        residual=W['cap']-pW
        if residual < 0:
            infeas=True
            continue
        inter_global = W['mask'] & U['mask'] & ~force_mask & ~forbid_mask
        if not inter_global:
            continue
        lm=0
        x=inter_global
        while x:
            lsb=x & -x; p=lsb.bit_length()-1; x^=lsb
            i=pos.get(p)
            if i is not None:
                lm |= 1<<i
        if lm and lm.bit_count() > residual:
            old=best.get(lm)
            if old is None or residual < old:
                best[lm]=residual
    constraints=[(lm,cap) for lm,cap in best.items()]
    # point eliminations from residual cap 0 are incorporated as constraints and also in allowed mask.
    return pU, future_global, constraints, infeas

def feasible_k(n:int, constraints:list[tuple[int,int]], k:int, want_witness:bool=False):
    allmask=(1<<n)-1
    # Construct cap-one incompatible graph for fast pair pruning.
    compat=[allmask ^ (1<<i) for i in range(n)]
    pair_blocked=0
    for lm,cap in constraints:
        if cap==0:
            # remove all points in lm by setting compat not enough; use forbidden mask below.
            continue
        if cap==1:
            inds=list(bit_positions(lm))
            for a,b in itertools.combinations(inds,2):
                if (compat[a]>>b)&1:
                    pair_blocked += 1
                compat[a] &= ~(1<<b); compat[b] &= ~(1<<a)
    allowed=allmask
    for lm,cap in constraints:
        if cap==0:
            allowed &= ~lm
    inc=[[] for _ in range(n)]
    for ci,(lm,cap) in enumerate(constraints):
        if cap < k:
            for v in bit_positions(lm & allowed):
                inc[v].append(ci)
    counts=[0]*len(constraints)
    chosen=[]; stats=Counter(); first_rejects=[]
    witness=None
    def rec(cand:int, depth:int):
        nonlocal witness
        stats['nodes'] += 1
        need=k-depth
        if need==0:
            witness=chosen.copy()
            return True
        if cand.bit_count() < need:
            stats['shortage_prunes'] += 1
            return False
        if need>=2:
            has_pair=False; ctmp=cand
            while ctmp and not has_pair:
                lsb=ctmp & -ctmp; v=lsb.bit_length()-1; ctmp^=lsb
                if ctmp & compat[v]: has_pair=True
            if not has_pair:
                stats['pair_bound_prunes'] += 1
                return False
        # Exact combination enumeration in increasing local-index order.  Do not
        # sort candidates by degree while also discarding indices <=v; that can
        # miss combinations and create false infeasibility.
        c = cand
        while c:
            lsb = c & -c
            v = lsb.bit_length() - 1
            c ^= lsb
            bad=None; changed=[]
            for ci in inc[v]:
                counts[ci]+=1; changed.append(ci)
                if counts[ci] > constraints[ci][1] and bad is None:
                    bad=ci
            if bad is None:
                chosen.append(v)
                if rec(c & compat[v], depth+1):
                    return True
                chosen.pop()
            else:
                stats['constraint_prunes'] += 1
                stats[f'cap{constraints[bad][1]}_prunes'] += 1
                if len(first_rejects)<10:
                    first_rejects.append({'partial_local': chosen+[v], 'constraint_cap': constraints[bad][1], 'constraint_pop': constraints[bad][0].bit_count()})
            for ci in reversed(changed):
                counts[ci]-=1
        return False
    ok=rec(allowed,0)
    out={'feasible':ok,'stats':{str(k):int(v) for k,v in sorted(stats.items())},'pair_blocked_cap1':pair_blocked,'allowed_after_cap0':allowed.bit_count(),'first_rejects':first_rejects}
    if ok and want_witness:
        out['witness_local']=witness
    return out

def max_local(n:int, constraints, upper:int):
    attempts=[]
    for k in range(min(upper,n), -1, -1):
        res=feasible_k(n,constraints,k,want_witness=True)
        attempts.append({'k':k, **res})
        if res['feasible']:
            return k, attempts, res.get('witness_local')
    return -1, attempts, None

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--pivot', required=True, choices=['rank2','rank3'])
    ap.add_argument('--branch', type=int, required=True)
    ap.add_argument('--rows', type=Path, required=True)
    ap.add_argument('--mining', type=Path, nargs='+', required=True)
    ap.add_argument('--max-rows', type=int, default=200)
    ap.add_argument('--allowed-caps', default='4,5,7,10,13,16')
    ap.add_argument('--label', required=True)
    ap.add_argument('--outdir', type=Path, default=ROOT/'workspace/data/quotient_lift/residual')
    ap.add_argument('--detail-limit', type=int, default=80)
    args=ap.parse_args(); args.outdir.mkdir(parents=True, exist_ok=True)
    t0=time.time(); rows,rowmeta=load_rows(args.rows)
    specs=json.loads(SPECS.read_text())['pivots'][args.pivot]['branches']
    br=next(b for b in specs if int(b['branch'])==args.branch)
    force_mask=point_mask(br['force']); forbid_mask=point_mask(br['forbid'])
    allowed_caps={int(x) for x in args.allowed_caps.split(',') if x.strip()}
    cands=choose_candidate_indices(args.mining, rows, args.max_rows, allowed_caps)
    out_rows=[]; details=[]; tightened=[]; infeas_rows=[]; hist=Counter(); maxdrop=Counter(); constr_hist=Counter(); future_hist=Counter()
    for j,idx in enumerate(cands):
        U=rows[idx]
        pU, future, constraints, infeas=build_local_constraints(rows,U,force_mask,forbid_mask)
        if infeas:
            infeas_rows.append(idx)
        future_cap=max(0,U['cap']-pU)
        M, attempts, wit=max_local(len(future), constraints, future_cap)
        new_total=pU+M if M>=0 else pU-1
        drop=U['cap']-new_total
        hist[(U['dim'],U['cap'],new_total)] += 1
        maxdrop[drop] += 1
        constr_hist[len(constraints)] += 1
        future_hist[len(future)] += 1
        rec={'idx':idx,'dim':U['dim'],'old_cap':U['cap'],'pU_forced_inside':pU,'future_point_count':len(future),'constraint_count':len(constraints),'max_future':M,'new_total_cap':new_total,'drop':drop,'mask_hex':hex(U['mask']),'attempts':attempts[:4]}
        if wit is not None:
            rec['witness_global']=[future[i] for i in wit]
        if drop>0:
            tightened.append(rec)
            out_rows.append(pack_row(new_total,U['dim'],U['mask']))
        if len(details)<args.detail_limit or drop>0:
            details.append(rec)
        if (j+1)%25==0 or j+1==len(cands):
            print(args.label, j+1, '/', len(cands), 'tightened', len(tightened), 'elapsed', f'{time.time()-t0:.2f}', flush=True)
    outbin=args.outdir/f'{args.label}_branch_residual_rows.bin'
    write_rows(outbin,out_rows)
    out={'schema':'s0908_residual_local_tighten_v1','meaning':'Branch-conditional local residual rows. For the specified branch force/forbid, each tightened row U has exact maximum new_total_cap points in U under all crossing row residual capacities from the supplied table. Valid only with these branch assumptions.','pivot':args.pivot,'branch':args.branch,'force':br['force'],'forbid_count':br['forbid_count'],'rows_meta':rowmeta,'mining_paths':[str(p) for p in args.mining],'mining_sha256':[sha(p) for p in args.mining],'candidate_indices':cands,'candidate_count':len(cands),'tightened_count':len(tightened),'tightened_rows_head':tightened[:args.detail_limit],'details_head':details[:args.detail_limit],'infeasible_branch_rows':infeas_rows[:20],'dim_old_new_hist':{f'{d}:{c}->{nc}':int(v) for (d,c,nc),v in sorted(hist.items())},'drop_hist':{str(k):int(v) for k,v in sorted(maxdrop.items())},'constraint_count_hist_head':{str(k):int(v) for k,v in sorted(constr_hist.items())[:40]},'future_point_count_hist':{str(k):int(v) for k,v in sorted(future_hist.items())},'output_rows':str(outbin),'output_rows_sha256':sha(outbin),'elapsed_sec':time.time()-t0}
    outjson=args.outdir/f'{args.label}_branch_residual_tightening.json'
    outjson.write_text(json.dumps(out, indent=2, sort_keys=True)+'\n')
    print(json.dumps({'json':str(outjson),'binary':str(outbin),'candidate_count':len(cands),'tightened_count':len(tightened),'drop_hist':out['drop_hist'],'sha256':sha(outbin),'elapsed_sec':out['elapsed_sec']},indent=2,sort_keys=True), flush=True)

if __name__=='__main__':
    main()
