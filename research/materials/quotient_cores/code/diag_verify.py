#!/usr/bin/env python3
"""
analysisb: Direct point-evaluation check of the diagonal basis transformation
and block extraction.  Validates everything at BILR before running the
pencil-conic instrument.
"""
import json
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
OUT = WS / "data" / "diagonal_block"
OUT.mkdir(parents=True, exist_ok=True)

P = 65521

def inv(a): return pow(a % P, P-2, P) % P

# Find i
II = None
for x in range(2, P):
    if pow(x, (P-1)//2, P) == P-1:
        r = pow(x, (P-1)//4, P)
        if (r*r)%P == P-1:
            II = r; break
assert II and (II*II)%P == P-1
print(f"p={P}, i={II}")

# a0, eigenvalues mu = [-1, i, -i]
a0 = [[0,0,P-1],[1,0,P-1],[0,1,P-1]]
mu = [P-1, II, (P-II)%P]

# Eigenvectors: v0=(1,0,1), v1=(i,1+i,1), v2=(-i,1-i,1)
Pm = [[1, II, (P-II)%P],
      [0, (1+II)%P, (1+P-II)%P],
      [1, 1, 1]]

def mm(A,B):
    n,m,k = len(A),len(B[0]),len(B)
    return [[(sum(A[i][l]*B[l][j] for l in range(k)))%P for j in range(m)] for i in range(n)]

def mi3(M):
    a,b,c = M[0]; d,e,f = M[1]; g,h,k_ = M[2]
    det = (a*(e*k_-f*h)-b*(d*k_-f*g)+c*(d*h-e*g))%P
    di = inv(det)
    return [[((e*k_-f*h)*di)%P,((c*h-b*k_)*di)%P,((b*f-c*e)*di)%P],
            [((f*g-d*k_)*di)%P,((a*k_-c*g)*di)%P,((c*d-a*f)*di)%P],
            [((d*h-e*g)*di)%P,((b*g-a*h)*di)%P,((a*e-b*d)*di)%P]]

def mT(M): return [[M[j][i] for j in range(len(M))] for i in range(len(M[0]))]

Pi = mi3(Pm)

# Verify diagonalization
D = mm(mm(Pi, a0), Pm)
for i in range(3):
    assert D[i][i]%P == mu[i]
    for j in range(3):
        if i!=j: assert D[i][j]%P == 0
print("P^{-1}a0P = diag(-1,i,-i) ✓")

# Load BILR scheme
scheme = json.loads((WS/"data"/"ballard_z4_cyclic"/"ballard_z4_cyclic_scheme.json").read_text())
cubes_orig = scheme["cubes"]
free_reps = scheme["free_orbit_representatives"]

# ── Point evaluation test ──
# Pick a random test point in the diagonal basis
import random
random.seed(42)
M_diag = [[random.randint(0, P-1) for _ in range(3)] for _ in range(3)]

# Convert to original basis: M = P * M_diag * P^{-1}
M_orig = mm(mm(Pm, M_diag), Pi)

# Evaluate tr(X^3) in original basis
def trX3(M):
    s = 0
    for a in range(3):
        for b in range(3):
            for c in range(3):
                s += M[a][b]*M[b][c]*M[c][a]
    return s % P

T = trX3(M_orig)
print(f"\ntr(X^3) at test point = {T}")

# Also evaluate directly from diagonal basis using the formula
# tr(X^3) = sum_{a,b,c} n_{ab}*n_{bc}*n_{ca}
def trX3_diag(N):
    s = 0
    for a in range(3):
        for b in range(3):
            for c in range(3):
                s += N[a][b]*N[b][c]*N[c][a]
    return s % P

T_diag = trX3_diag(M_diag)
print(f"tr(X'^3) at test point (diagonal) = {T_diag}")
print(f"Match: {T == T_diag}")

# Evaluate cube contributions
# Each cube L has l(M) = tr(L^T M) = sum L_{ij}*M_{ij}
def form_eval_orig(L, M):
    return sum(L[i][j]*M[i][j] for i in range(3) for j in range(3)) % P

cube_sum = 0
for L in cubes_orig:
    v = form_eval_orig(L, M_orig)
    cube_sum = (cube_sum + v*v*v) % P

# Evaluate free orbit contributions
# Each rep (U,V,W) contributes 3*u(M)*v(M)*w(M)
free_sum = 0
for rep in free_reps:
    u = form_eval_orig(rep["U"], M_orig)
    v = form_eval_orig(rep["V"], M_orig)
    w = form_eval_orig(rep["W"], M_orig)
    free_sum = (free_sum + 3*u*v*w) % P

total = (cube_sum + free_sum) % P
print(f"\nCube sum = {cube_sum}")
print(f"Free sum = {free_sum}")
print(f"Total = {total}")
print(f"tr(X^3) = {T}")
print(f"Match: {total == T}")

# ── Now transform forms to diagonal basis and re-evaluate ──
# Transformation: L' = P^{-1} L^T P  for tr(L^T M) -> tr(L' M') pairing
def transform_form(L):
    return mm(mm(Pi, mT(L)), Pm)

# Verify: l(M) = tr(L^T M) = tr(L' M')
L0 = cubes_orig[0]
L0d = transform_form(L0)
v_orig = form_eval_orig(L0, M_orig)
v_diag = sum(L0d[a][b]*M_diag[b][a] for a in range(3) for b in range(3)) % P
print(f"\nCube 0 original eval = {v_orig}")
print(f"Cube 0 diagonal eval (tr(L'M')) = {v_diag}")
print(f"Match: {v_orig == v_diag}")

# Verify for all cubes
all_match = True
cubes_diag = []
for j, L in enumerate(cubes_orig):
    Ld = transform_form(L)
    cubes_diag.append(Ld)
    v1 = form_eval_orig(L, M_orig)
    v2 = sum(Ld[a][b]*M_diag[b][a] for a in range(3) for b in range(3)) % P
    if v1 != v2:
        print(f"  Cube {j}: MISMATCH {v1} != {v2}")
        all_match = False
print(f"All cube transforms verified: {all_match}")

# ── Extract form components and check Z4 action ──
# n_{ab} = X'_{ab} has eigenvalue mu_b/mu_a
# coefficient of n_{ab} in form l = L'_{ba}
# L'_{ba} has eigenvalue mu_a/mu_b under L' -> D^{-1}L'D (form action)

# Variable groups:
# p: eigenvalue 1 -> (a,b) where mu_b/mu_a = 1 -> a=b
# q: eigenvalue -1 -> (1,2),(2,1)
# z: eigenvalue i -> varies by mu assignment

# Compute eigenvalue table for variables
eig = {}
for a in range(3):
    for b in range(3):
        eig[(a,b)] = (mu[b]*inv(mu[a]))%P

p_v = sorted([(a,b) for a,b in eig if eig[(a,b)]==1])
q_v = sorted([(a,b) for a,b in eig if eig[(a,b)]==P-1])
z_v = sorted([(a,b) for a,b in eig if eig[(a,b)]==II])
w_v = sorted([(a,b) for a,b in eig if eig[(a,b)]==(P-II)%P])
print(f"\nVariable groups: p={p_v}, q={q_v}, z={z_v}, w={w_v}")

# Form components: coefficient of n_{ab} = L'_{ba}
# Group by variable eigenvalue:
def get_fc(Ld):
    """Form components grouped by variable type."""
    return {
        'p': [Ld[a][a]%P for a,_ in [(0,0),(1,1),(2,2)]],  # L'_{aa}
        'q': [Ld[b][a]%P for a,b in q_v],  # L'_{ba} for q-vars
        'z': [Ld[b][a]%P for a,b in z_v],  # L'_{ba} for z-vars
        'w': [Ld[b][a]%P for a,b in w_v],  # L'_{ba} for w-vars
    }

# Z4 action on form L' -> D^{-1}L'D
# (D^{-1}L'D)_{ba} = mu_b^{-1} L'_{ba} mu_a = (mu_a/mu_b) L'_{ba}
# For coefficient of n_{ab}: it's L'_{ba}, which transforms by mu_a/mu_b.
# Variable n_{ab} has eigenvalue mu_b/mu_a.
# So the form-coefficient eigenvalue = mu_a/mu_b = (mu_b/mu_a)^{-1}.

# For z-vars (eig i): form-coeff has eig 1/i = -i
# For w-vars (eig -i): form-coeff has eig 1/(-i) = i

def apply_g(fc):
    """Correct Z4 action on form components (dual eigenvalues)."""
    return {
        'p': list(fc['p']),
        'q': [(P-x)%P for x in fc['q']],  # multiply by -1
        'z': [((P-II)*x)%P for x in fc['z']],  # multiply by -i (NOT i!)
        'w': [(II*x)%P for x in fc['w']],  # multiply by i (NOT -i!)
    }

# Verify Z4 action by direct matrix computation
def apply_g_matrix(Ld):
    """Apply L' -> D^{-1}L'D."""
    Di = [[inv(mu[i]) if i==j else 0 for j in range(3)] for i in range(3)]
    Dmat = [[mu[i] if i==j else 0 for j in range(3)] for i in range(3)]
    return mm(mm(Di, Ld), Dmat)

# Test on cube 0
fc0 = get_fc(cubes_diag[0])
fc0_g = apply_g(fc0)
Ld0_g = apply_g_matrix(cubes_diag[0])
fc0_g_direct = get_fc(Ld0_g)
print(f"\nCube 0 form components: {fc0}")
print(f"After g (formula):  {fc0_g}")
print(f"After g (matrix):   {fc0_g_direct}")
print(f"Match: {fc0_g == fc0_g_direct}")

# ── Find cube orbits under Z4 ──
def fc_proportional(fc1, fc2):
    all1 = fc1['p']+fc1['q']+fc1['z']+fc1['w']
    all2 = fc2['p']+fc2['q']+fc2['z']+fc2['w']
    lam = None
    for a, b in zip(all1, all2):
        if a%P != 0:
            l = (b*inv(a))%P
            if lam is None: lam = l
            elif l != lam: return False, 0
        elif b%P != 0:
            return False, 0
    return True, (lam if lam else 0)

cube_fcs = [get_fc(cubes_diag[j]) for j in range(11)]
visited = [False]*11
orbits = []
for j in range(11):
    if visited[j]: continue
    orbit = [j]
    visited[j] = True
    cur_fc = cube_fcs[j]
    for _ in range(3):
        cur_fc = apply_g(cur_fc)
        for k in range(11):
            if not visited[k]:
                ok, lam = fc_proportional(cur_fc, cube_fcs[k])
                if ok:
                    orbit.append(k)
                    visited[k] = True
                    break
    orbits.append(orbit)

print(f"\nCube orbits: {orbits}")
print(f"Sizes: {[len(o) for o in orbits]}")

# ── Compute residual blocks via direct point evaluation ──
# Instead of block formulas, evaluate directly at test points
# to validate the block extraction.

# Residual qz^2 block as 2x3 matrix.
# This means: residual cubic restricted to monomials with exactly
# one q-variable and two z-variables.

# For a cubic C(X) = sum c_alpha X^alpha, the qz^2 block M[qi][sj] is
# the coefficient of n_{q_vars[qi]} * sym2_z[sj] in C.

# Compute residual polynomial coefficients directly
from collections import defaultdict

def mono_key(inds):
    return tuple(sorted(inds))

def cube_poly(Ld):
    """Compute l^3 polynomial coefficients in diagonal basis.
    l(X') = sum L'_{ba} n_{ab} = sum_{a,b} L'_{ba} X'_{ab}."""
    # Linear form coefficients: coeff[ab] = L'_{ba}
    coeff = {}
    for a in range(3):
        for b in range(3):
            coeff[(a,b)] = Ld[b][a] % P
    
    # Cube: sum over all ordered triples
    poly = defaultdict(int)
    for ab in coeff:
        for cd in coeff:
            for ef in coeff:
                key = mono_key([ab, cd, ef])
                poly[key] = (poly[key] + coeff[ab]*coeff[cd]*coeff[ef]) % P
    return dict(poly)

# Total residual = sum of 11 cubes
residual_poly = defaultdict(int)
for j in range(11):
    cp = cube_poly(cubes_diag[j])
    for key, val in cp.items():
        residual_poly[key] = (residual_poly[key] + val) % P

# Also compute tr(X'^3) polynomial
trX3_poly = defaultdict(int)
for a in range(3):
    for b in range(3):
        for c in range(3):
            key = mono_key([(a,b),(b,c),(c,a)])
            trX3_poly[key] = (trX3_poly[key] + 1) % P

# And free orbit polynomial
def trilinear_poly(U, V, W):
    """Compute u(X)*v(X)*w(X) polynomial, U,V,W are diagonal-basis matrices."""
    cu = {(a,b): U[b][a]%P for a in range(3) for b in range(3)}
    cv = {(a,b): V[b][a]%P for a in range(3) for b in range(3)}
    cw = {(a,b): W[b][a]%P for a in range(3) for b in range(3)}
    poly = defaultdict(int)
    for ab in cu:
        for cd in cv:
            for ef in cw:
                key = mono_key([ab, cd, ef])
                poly[key] = (poly[key] + cu[ab]*cv[cd]*cw[ef]) % P
    return dict(poly)

free_poly = defaultdict(int)
for rep in free_reps:
    Ud = transform_form(rep["U"])
    Vd = transform_form(rep["V"])
    Wd = transform_form(rep["W"])
    tp = trilinear_poly(Ud, Vd, Wd)
    for key, val in tp.items():
        free_poly[key] = (free_poly[key] + 3*val) % P

# Check: tr(X'^3) = residual + free
print("\n── Polynomial check: tr(X'^3) = cubes + free ──")
all_keys = set(trX3_poly.keys()) | set(residual_poly.keys()) | set(free_poly.keys())
mismatches = 0
for key in all_keys:
    lhs = trX3_poly.get(key, 0) % P
    rhs = (residual_poly.get(key, 0) + free_poly.get(key, 0)) % P
    if lhs != rhs:
        mismatches += 1
print(f"Monomial mismatches: {mismatches}")
assert mismatches == 0, "Polynomial decomposition FAILED"
print("Polynomial decomposition VERIFIED ✓")

# ── Extract qz^2 block from residual ──
def var_type(ab):
    e = eig[ab]
    if e == 1: return 'p'
    if e == P-1: return 'q'
    if e == II: return 'z'
    if e == (P-II)%P: return 'w'

def block_type(key):
    types = sorted([var_type(v) for v in key])
    return ''.join(types)

# qz^2 monomials: one q-var, two z-vars
# q_v = sorted q-variables, z_v = sorted z-variables
print(f"\nq-vars: {q_v}, z-vars: {z_v}")

# Build 2x3 matrix: rows = q_v[0], q_v[1]; cols = z_v[0]^2, z_v[0]*z_v[1], z_v[1]^2
sym2_z = [(z_v[0],z_v[0]), (z_v[0],z_v[1]), (z_v[1],z_v[1])]

res_qz2 = [[0]*3 for _ in range(2)]
for qi in range(2):
    for si in range(3):
        key = mono_key([q_v[qi], sym2_z[si][0], sym2_z[si][1]])
        res_qz2[qi][si] = residual_poly.get(key, 0) % P

tgt_qz2 = [[0]*3 for _ in range(2)]
for qi in range(2):
    for si in range(3):
        key = mono_key([q_v[qi], sym2_z[si][0], sym2_z[si][1]])
        tgt_qz2[qi][si] = trX3_poly.get(key, 0) % P

free_qz2 = [[0]*3 for _ in range(2)]
for qi in range(2):
    for si in range(3):
        key = mono_key([q_v[qi], sym2_z[si][0], sym2_z[si][1]])
        free_qz2[qi][si] = free_poly.get(key, 0) % P

print(f"\nTarget  qz^2: {tgt_qz2}")
print(f"Free    qz^2: {free_qz2}")
print(f"Residual qz^2: {res_qz2}")
check = [[(tgt_qz2[i][j] - free_qz2[i][j]) % P for j in range(3)] for i in range(2)]
print(f"Target-Free:  {check}")
print(f"Match residual: {check == res_qz2}")

# Similarly for qw^2
sym2_w = [(w_v[0],w_v[0]), (w_v[0],w_v[1]), (w_v[1],w_v[1])]
res_qw2 = [[0]*3 for _ in range(2)]
tgt_qw2 = [[0]*3 for _ in range(2)]
for qi in range(2):
    for si in range(3):
        key = mono_key([q_v[qi], sym2_w[si][0], sym2_w[si][1]])
        res_qw2[qi][si] = residual_poly.get(key, 0) % P
        tgt_qw2[qi][si] = trX3_poly.get(key, 0) % P

print(f"\nTarget  qw^2: {tgt_qw2}")
print(f"Residual qw^2: {res_qw2}")

# ── Pencil-conic on residual qz^2 ──
print("\n" + "="*60)
print("Pencil-conic on residual qz^2")
print("="*60)
print(f"R = {res_qz2}")

# Rank check
def rank2x3(M):
    for i in range(2):
        for j in range(3):
            if M[i][j]%P != 0:
                r,c = i,j
                other = 1-r
                if M[other][c]%P != 0:
                    f = (M[other][c]*inv(M[r][c]))%P
                    row = [(M[other][k]-f*M[r][k])%P for k in range(3)]
                    return 2 if any(x%P!=0 for x in row) else 1
                return 2 if any(M[other][k]%P!=0 for k in range(3)) else 1
    return 0

rk = rank2x3(res_qz2)
print(f"Rank: {rk}")

# Conic: [a,b,c] on Veronese iff b^2 = 4ac (with our Sym^2 convention)
# Wait, actually the convention depends on the basis.
# With basis z1^2, z1*z2, z2^2:
# A point on the Veronese is [t^2, t*s, s^2] (NOT [t^2, 2ts, s^2]!)
# because the cube l^3 has coefficient z1*z2 (not 2*z1*z2) for the cross term
# when using the polynomial ring (not symmetric tensor) convention.

# Actually let me check directly. For a single cube l with z-components (z1,z2),
# the qz^2 contribution from the polynomial l^3 is:
# coeff of n_{q}*n_{z1}^2 = 3*q*z1^2 (from ordering: q,z1,z1 appears 3 times)
# coeff of n_{q}*n_{z1}*n_{z2} = 6*q*z1*z2 (from: q,z1,z2 and all orderings = 6)
# coeff of n_{q}*n_{z2}^2 = 3*q*z2^2

# But in the monomial key, (q, z1, z2) with z1 != z2 appears as an unordered tuple.
# The coefficient in the polynomial is 6 if all three indices are distinct.

# Let me just check a specific cube.
fc3 = cube_fcs[3]
print(f"\nCube 3 components: q={fc3['q']}, z={fc3['z']}")

# Compute cube 3's polynomial
cp3 = cube_poly(cubes_diag[3])

# Extract qz^2 entries
for qi in range(2):
    for si in range(3):
        key = mono_key([q_v[qi], sym2_z[si][0], sym2_z[si][1]])
        val = cp3.get(key, 0)%P
        # Expected: multinomial_coeff * q[qi] * z[si]_product
        q_val = fc3['q'][qi]
        if si == 0: z_val = (fc3['z'][0]**2)%P; mult = 3
        elif si == 1: z_val = (fc3['z'][0]*fc3['z'][1])%P; mult = 6
        else: z_val = (fc3['z'][1]**2)%P; mult = 3
        expected = (mult * q_val * z_val) % P
        if val != expected:
            print(f"  Cube 3 qz^2[{qi},{si}]: got {val}, expected {expected}")

# For the Veronese conic in OUR convention:
# The qz^2 entry for cube l with components q,z is:
# Row qi, col 0: 3*q[qi]*z[0]^2
# Row qi, col 1: 6*q[qi]*z[0]*z[1]
# Row qi, col 2: 3*q[qi]*z[1]^2
# = 3*q[qi] * [z[0]^2, 2*z[0]*z[1], z[1]^2]

# So the Veronese point is [z0^2 : 2*z0*z1 : z1^2] in our matrix convention.
# A point [A:B:C] is on the Veronese iff B^2 = 4AC.

# Pencil-conic intersection:
r0, r1 = res_qz2[0], res_qz2[1]
A_c = (r0[1]*r0[1] - 4*r0[0]*r0[2]) % P
B_c = (2*r0[1]*r1[1] - 4*r0[0]*r1[2] - 4*r1[0]*r0[2]) % P
C_c = (r1[1]*r1[1] - 4*r1[0]*r1[2]) % P
disc = (B_c*B_c - 4*A_c*C_c) % P

print(f"\nPencil quadratic: A={A_c}, B={B_c}, C={C_c}")
print(f"Discriminant = {disc}")

def is_qr(x): return x%P==0 or pow(x,(P-1)//2,P)==1
def sqrtm(x):
    if x%P==0: return 0
    if not is_qr(x): return None
    if P%4==3: return pow(x,(P+1)//4,P)
    q,s = P-1,0
    while q%2==0: q//=2; s+=1
    z = 2
    while is_qr(z): z+=1
    M_,c,t,R = s,pow(z,q,P),pow(x,q,P),pow(x,(q+1)//2,P)
    while True:
        if t==1: return R
        i=1; tmp=(t*t)%P
        while tmp!=1: tmp=(tmp*tmp)%P; i+=1
        b=pow(c,1<<(M_-i-1),P)
        M_,c,t,R = i,(b*b)%P,(t*b*b)%P,(R*b)%P

if is_qr(disc):
    sd = sqrtm(disc)
    print(f"sqrt(disc) = {sd}")
    if A_c%P != 0:
        inv2A = inv(2*A_c)
        lam1 = ((P-B_c+sd)*inv2A)%P
        lam2 = ((P-B_c-sd+P)*inv2A)%P
    elif B_c%P != 0:
        lam1 = ((P-C_c)*inv(B_c))%P; lam2 = None
    else:
        lam1 = lam2 = None
    
    print(f"Lambda: {lam1}, {lam2}")
    
    if lam1 is not None:
        zs1 = [(lam1*r0[j]+r1[j])%P for j in range(3)]
        print(f"z-sq 1: {zs1}, on conic: {(zs1[1]*zs1[1]-4*zs1[0]*zs1[2])%P == 0}")
    if lam2 is not None:
        zs2 = [(lam2*r0[j]+r1[j])%P for j in range(3)]
        print(f"z-sq 2: {zs2}, on conic: {(zs2[1]*zs2[1]-4*zs2[0]*zs2[2])%P == 0}")
    
    # Match against known size-4 orbit z-components
    print("\nKnown size-4 orbit z-components:")
    for orb in orbits:
        if len(orb) == 4:
            fc = cube_fcs[orb[0]]
            z = fc['z']
            zsk = [(z[0]**2)%P, (2*z[0]*z[1])%P, (z[1]**2)%P]
            print(f"  Orbit {orb}: z={z}, z^2={zsk}")
            for idx, zs in enumerate([zs1] + ([zs2] if lam2 else [])):
                if all(x==0 for x in zs): continue
                for k in range(3):
                    if zsk[k]%P != 0:
                        ratio = (zs[k]*inv(zsk[k]))%P
                        match = all((zs[j]-ratio*zsk[j])%P==0 for j in range(3))
                        if match:
                            print(f"    -> matches conic sol {idx+1}, ratio={ratio}")
                        break
else:
    print("Discriminant NOT QR - solutions in extension field")

# Save
results = {
    "prime": P, "imag_unit": II,
    "var_groups": {
        "p": [list(x) for x in p_v],
        "q": [list(x) for x in q_v],
        "z": [list(x) for x in z_v],
        "w": [list(x) for x in w_v],
    },
    "cube_orbits": orbits,
    "orbit_sizes": [len(o) for o in orbits],
    "poly_check_ok": True,
    "target_qz2": tgt_qz2,
    "residual_qz2": res_qz2,
    "free_qz2": free_qz2,
    "target_qw2": tgt_qw2,
    "residual_qw2": res_qw2,
    "qz2_pencil_disc": int(disc),
    "qz2_disc_is_QR": is_qr(disc),
}
(OUT/"diagonal_block_analysis_v2.json").write_text(json.dumps(results,indent=2)+'\n')
print(f"\nSaved {OUT/'diagonal_block_analysis_v2.json'}")
