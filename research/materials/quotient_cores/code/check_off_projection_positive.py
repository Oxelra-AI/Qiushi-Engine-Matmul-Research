#!/usr/bin/env python3
"""Check analysis off-W projection on the BILR rank-23 residual control."""
from pathlib import Path
import json, sys
import numpy as np
WS=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(WS/'scripts'))
import z4_symmetry_kernel_residual as s42
import z4_off_projection_system as offsys
import z4_rank10_orbit_numeric_search as num
p=65521
proj=offsys.off_projection_matrix(p)
a0,powers,Ad,Ad_pows,S4=s42.build_a0_ad_s4()
scheme=json.loads((WS/'data/ballard_z4_cyclic/ballard_z4_cyclic_scheme.json').read_text())
U0=np.array(scheme['free_orbit_representatives'][0]['U'],dtype=object).reshape(9)
V0=np.array(scheme['free_orbit_representatives'][0]['V'],dtype=object).reshape(9)
W0=np.array(scheme['free_orbit_representatives'][0]['W'],dtype=object).reshape(9)
T0=np.stack([U0,V0,W0],axis=1)
tr=s42.target_trM3_vec()%p
free=s42.free_orbit_diag_coeff_from_cols(T0,Ad_pows)%p
reps=num.get_orbit_reps_from_bilr(Ad_pows)
length4=[r['rep'].astype(object) for r in reps if r['length']==4]
length2=[r['rep'].astype(object) for r in reps if r['length']==2]
length1=[r['rep'].astype(object) for r in reps if r['length']==1]
assert len(length4)==2 and len(length2)==1 and len(length1)==1
phi4=sum((s42.orbit_cube_coeff(v,Ad_pows,4)%p for v in length4), start=np.zeros(len(s42.MONOS),dtype=object))%p
phi_tail=(s42.orbit_cube_coeff(length2[0],Ad_pows,2)+s42.orbit_cube_coeff(length1[0],Ad_pows,1))%p
vec=(tr-free-phi4)%p
off=proj['off']
off_vec=(off@vec)%p
off_tail=(off@phi_tail)%p
# Also full residual equals all cube orbits.
allc=(phi4+phi_tail)%p
full_mismatch=(tr-free-allc)%p
result={'p':p,'lengths':[r['length'] for r in reps],
        'off_vec_nonzero':int(np.count_nonzero(off_vec)),'off_vec_max':int(max([int(x) for x in off_vec] or [0])),
        'off_tail_nonzero':int(np.count_nonzero(off_tail)),
        'full_residual_minus_cube_orbits_nonzero':int(np.count_nonzero(full_mismatch)),
        'projection_dims':proj['ranks']}
out=WS/'data/z4_off_system/off_projection_positive_control.json'
out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
