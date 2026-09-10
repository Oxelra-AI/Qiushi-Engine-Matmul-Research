#!/usr/bin/env python3
"""Exact symbolic identities for the analysis Z4 block instrument."""
from __future__ import annotations
import json
from pathlib import Path
import sympy as sp

SCRIPT_DIR = Path(__file__).resolve().parent
WS = SCRIPT_DIR.parent
OUT = WS / "data" / "z4_qbasis"
OUT.mkdir(parents=True, exist_ok=True)

p0,p1,p2,q0,q1,z0,z1,w0,w1 = sp.symbols('p0 p1 p2 q0 q1 z0 z1 w0 w1')
xp0,xp1,xp2,xq0,xq1,xz0,xz1,xw0,xw1 = sp.symbols('xp0 xp1 xp2 xq0 xq1 xz0 xz1 xw0 xw1')
t,eps = sp.symbols('t eps')
I = sp.I

Pform = p0*xp0 + p1*xp1 + p2*xp2
Qform = q0*xq0 + q1*xq1
Zform = z0*xz0 + z1*xz1
Wform = w0*xw0 + w1*xw1

def orbit_sum(Pf,Qf,Zf,Wf):
    s=0
    for k in range(4):
        Lk = Pf + (-1)**k*Qf + (I**k)*Zf + ((-I)**k)*Wf
        s += sp.expand(Lk**3)
    return sp.expand(s)

S = orbit_sum(Pform,Qform,Zform,Wform)
expected = sp.expand(4*Pform**3 + 12*Pform*Qform**2 + 24*Pform*Zform*Wform + 12*Qform*Zform**2 + 12*Qform*Wform**2)
formula_diff = sp.expand(S-expected)

S2 = sp.expand((Pform+Qform)**3 + (Pform-Qform)**3)
expected2 = sp.expand(2*Pform**3 + 6*Pform*Qform**2)
len2_diff = sp.expand(S2-expected2)

# General off-preserving rescaling: Z -> t Z, W -> eps t W, Q -> t^-2 Q, P -> eps t^-2 P, eps^2=1.
Psc = eps*t**-2*Pform
Qsc = t**-2*Qform
Zsc = t*Zform
Wsc = eps*t*Wform
Ssc = orbit_sum(Psc,Qsc,Zsc,Wsc)
h = eps*t**-6
expected_scaled = sp.expand(4*h*Pform**3 + 12*h*Pform*Qform**2 + 24*Pform*Zform*Wform + 12*Qform*Zform**2 + 12*Qform*Wform**2)
# Reduce eps^2=1 by substituting eps**2 repeatedly via polynomial reduction.
scale_diff_raw = sp.expand(Ssc-expected_scaled)
num = sp.together(scale_diff_raw * t**6).expand()
poly = sp.Poly(num, eps)
rem = sp.rem(poly, sp.Poly(eps**2-1, eps)).as_expr()
scale_diff_reduced = sp.simplify(rem)

result = {
    'orbit_formula_diff_zero': bool(formula_diff == 0),
    'length2_formula_diff_zero': bool(len2_diff == 0),
    'hidden_scaling_diff_zero_mod_eps2_minus_1': bool(scale_diff_reduced == 0),
    'length4_formula': 'sum_{k=0}^3 (P+(-1)^k Q+i^k Z+(-i)^k W)^3 = 4P^3+12PQ^2+24PZW+12QZ^2+12QW^2',
    'length2_formula': '(P+Q)^3+(P-Q)^3 = 2P^3+6PQ^2',
    'hidden_scaling': 'Z,W -> tZ, eps*tW and Q,P -> t^{-2}Q, eps*t^{-2}P preserves off blocks and multiplies tail by h=eps*t^{-6} (eps^2=1)',
}
out = OUT/'symbolic_orbit_formula.json'
out.write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps({'out':str(out), **result}, indent=2))
