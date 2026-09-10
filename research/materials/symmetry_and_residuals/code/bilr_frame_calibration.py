#!/usr/bin/env python3
"""Identify the BILR plane in the analysis C4 linear section and compare frames."""
from __future__ import annotations
import importlib.util, json, sys
from pathlib import Path

WS=Path(__file__).resolve().parent.parent
OUT=WS/'data'/'exterior_linear_sections'
spec=importlib.util.spec_from_file_location('s57', WS/'scripts'/'invariant_linear_section.py')
s57=importlib.util.module_from_spec(spec); spec.loader.exec_module(s57)  # type: ignore
sys.path.insert(0,str(WS/'scripts'))
import ballard_z4_cyclic_scheme as bilr  # type: ignore
p=5
pivot=(0,2,7)

def bilr_first_plane_new_normalized():
    gens_ad,_=s57.group_ad_generators('c4_regular',p)
    E,weights=s57.simultaneous_eigenbasis(gens_ad,'c4_regular',p)
    Einv=s57.mat_inv(E,p)
    old=[[0,0,0,1,0,0,0,0], [0,0,0,0,(-1)%p,1,0,0], [0,0,0,(-1)%p,0,1,0,1]]
    new=[s57.mat_vec(Einv,col,p) for col in old]
    pl=s57.wedge3_cols(new,p)
    piv=pl[s57.TIDX[pivot]]%p
    # The chart is not just a normalized wedge coordinate.  It fixes the pivot
    # submatrix itself to I_3, so we must left-multiply the 3x8 basis-row matrix
    # by the inverse of its pivot block.
    R=[[new[row][c]%p for c in range(8)] for row in range(3)]
    Bpiv=[[R[row][c]%p for c in pivot] for row in range(3)]
    T=s57.mat_inv(Bpiv,p)
    Rred=s57.mat_mul(T,R,p)
    nonpiv=[j for j in range(8) if j not in pivot]
    vals=[]
    for c in nonpiv:
        for r in range(3): vals.append(Rred[r][c]%p)
    return vals, piv, pl

data=json.loads((OUT/'f5_extracted_symmetry_points.json').read_text())
vals,piv,pl=bilr_first_plane_new_normalized()
idx=None; rec=None
for i,r in enumerate(data['c4_regular']['records']):
    if r['vals']==vals:
        idx=i; rec=r; break
# Displayed BILR residual KY rank over F5.
coeff=bilr.cube_coeffs(bilr.build_scheme()[1])
K=bilr.koszul_matrix_from_coeffs(coeff,p=4)
rank_displayed=bilr.rank_mod_np(K,p)
# Existing canonical-rank list from the residual scan.
ranks=json.loads((OUT/'f5_symmetry_residual_koszul_ranks_c4_regular_klein_diag.json').read_text())
canonical_rank=None
if idx is not None:
    for exfam in [ranks['families']['c4_regular']]:
        # ranks not recorded per all points except examples; recompute only if absent.
        pass
# Recompute canonical frame residual rank for the matched point using the analysis script functions.
spec2=importlib.util.spec_from_file_location('s57ky', WS/'scripts'/'residual_koszul_symmetry_points.py')
s57ky=importlib.util.module_from_spec(spec2); spec2.loader.exec_module(s57ky)  # type: ignore
canonical_rank=s57ky.rank_for_coeffs(s57ky.residual_coeffs_for_point('c4_regular',p,pivot,vals),p)
out={'prime':p,'pivot':list(pivot),'bilr_plucker_pivot_before_normalization':piv,'normalized_bilr_chart_vals':vals,'matched_extracted_solution_index':idx,'matched_record':rec,'displayed_bilr_internal_frame_koszul_rank_mod5':rank_displayed,'canonical_chart_frame_koszul_rank_mod5':canonical_rank,'interpretation':'Same exterior plane, different determinant-one internal frame choices can change the residual cubic and its Koszul rank. The exterior linear-section calculation does not by itself settle rank<=10 residual existence.'}
path=OUT/'bilr_plane_vs_internal_frame_calibration.json'
path.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
print(json.dumps(out,indent=2,sort_keys=True)); print('SAVED',path)
