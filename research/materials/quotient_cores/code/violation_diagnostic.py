#!/usr/bin/env python3
"""analysisb: Detailed diagnostics for L15/analysis unconditional leakage violations."""
import json, sys, collections
from pathlib import Path
SCRIPTS = Path("scripts")
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))
import contraction_weight_excess_search as base
from unconditional_leakage import get_intersection_dims

OUTDIR = Path("data/unconditional_leakage")

def diagnose_support(name, us):
    dB_tbl, dC_tbl = get_intersection_dims()
    weights = base.support_weights(us)
    n = len(us)

    targets = [mu for mu, sp in base.SPACES.items() if sp.rank_lam <= 2]
    violations = []

    for mu in targets:
        sp_mu = base.SPACES[mu]
        m_mu = weights[mu]
        if m_mu < sp_mu.r:
            continue
        budget = m_mu - sp_mu.r

        # Compute best unconditional lower bounds
        best_eB_lb = 0
        best_eC_lb = 0
        best_src_B = None
        best_src_C = None

        # Also track tight-only bounds
        tight_eB_lb = 0
        tight_eC_lb = 0

        for lam in range(1, 256):
            if lam == mu:
                continue
            sp_lam = base.SPACES[lam]
            m_lam = weights[lam]
            nu = lam ^ mu
            m_nu = base.m_from_weights(weights, nu, n)
            is_tight = (m_lam == sp_lam.r)

            rhs_B = 2 * sp_lam.r - m_lam + m_mu - m_nu - 2 * dB_tbl[(lam, mu)]
            rhs_C = 2 * sp_lam.r - m_lam + m_mu - m_nu - 2 * dC_tbl[(lam, mu)]
            lb_B = max(0, (rhs_B + 1) // 2) if rhs_B > 0 else 0
            lb_C = max(0, (rhs_C + 1) // 2) if rhs_C > 0 else 0

            if lb_B > best_eB_lb:
                best_eB_lb = lb_B
                best_src_B = {"lam": lam, "rank_lam": sp_lam.rank_lam,
                              "m_lam": m_lam, "r_lam": sp_lam.r,
                              "slack": m_lam - sp_lam.r,
                              "rhs_twice": rhs_B, "dB": dB_tbl[(lam, mu)],
                              "nu": nu, "m_nu": m_nu, "tight": is_tight}
            if lb_C > best_eC_lb:
                best_eC_lb = lb_C
                best_src_C = {"lam": lam, "rank_lam": sp_lam.rank_lam,
                              "m_lam": m_lam, "r_lam": sp_lam.r,
                              "slack": m_lam - sp_lam.r,
                              "rhs_twice": rhs_C, "dC": dC_tbl[(lam, mu)],
                              "nu": nu, "m_nu": m_nu, "tight": is_tight}

            if is_tight:
                t_lb_B = max(0, (sp_lam.r + m_mu - m_nu - 2*dB_tbl[(lam,mu)] + 1)//2) if (sp_lam.r + m_mu - m_nu - 2*dB_tbl[(lam,mu)]) > 0 else 0
                t_lb_C = max(0, (sp_lam.r + m_mu - m_nu - 2*dC_tbl[(lam,mu)] + 1)//2) if (sp_lam.r + m_mu - m_nu - 2*dC_tbl[(lam,mu)]) > 0 else 0
                tight_eB_lb = max(tight_eB_lb, t_lb_B)
                tight_eC_lb = max(tight_eC_lb, t_lb_C)

        total_uncond = best_eB_lb + best_eC_lb
        total_tight = tight_eB_lb + tight_eC_lb

        if total_uncond > budget:
            violations.append({
                "target_mu": mu, "rank_mu": sp_mu.rank_lam,
                "m_mu": m_mu, "r_mu": sp_mu.r, "budget": budget,
                "uncond_eB_lb": best_eB_lb, "uncond_eC_lb": best_eC_lb,
                "uncond_total": total_uncond, "excess": total_uncond - budget,
                "tight_eB_lb": tight_eB_lb, "tight_eC_lb": tight_eC_lb,
                "tight_total": total_tight,
                "best_src_B": best_src_B, "best_src_C": best_src_C,
            })

    return {
        "name": name, "support": us,
        "violation_count": len(violations),
        "violations": violations,
    }


def main():
    known = {
        "L15": [1,2,3,4,8,20,24,31,32,64,73,109,127,128,141,160,182,192,219],
        "analysis": [1,2,3,4,8,20,24,31,32,36,64,73,127,128,141,160,182,192,219],
    }
    result = {}
    for name, us in known.items():
        diag = diagnose_support(name, us)
        result[name] = diag
        print(f"\n=== {name}: {diag['violation_count']} violation(s) ===")
        for v in diag["violations"]:
            print(f"  target mu={v['target_mu']} (rank {v['rank_mu']}): "
                  f"budget={v['budget']}, uncond eB>={v['uncond_eB_lb']} eC>={v['uncond_eC_lb']} "
                  f"total={v['uncond_total']} > budget (excess {v['excess']})")
            print(f"    tight-only: eB>={v['tight_eB_lb']} eC>={v['tight_eC_lb']} total={v['tight_total']}")
            if v["best_src_B"]:
                s = v["best_src_B"]
                print(f"    best B-source: lam={s['lam']} rank={s['rank_lam']} "
                      f"m={s['m_lam']} r={s['r_lam']} slack={s['slack']} "
                      f"tight={s['tight']} dB={s['dB']} rhs/2={s['rhs_twice']}")
            if v["best_src_C"]:
                s = v["best_src_C"]
                print(f"    best C-source: lam={s['lam']} rank={s['rank_lam']} "
                      f"m={s['m_lam']} r={s['r_lam']} slack={s['slack']} "
                      f"tight={s['tight']} dC={s['dC']} rhs/2={s['rhs_twice']}")

    OUTDIR.mkdir(parents=True, exist_ok=True)
    outpath = OUTDIR / "l15_violation_details.json"
    with open(outpath, "w") as f:
        json.dump(result, f, indent=2, sort_keys=True)
    print(f"\nSaved to {outpath}")


if __name__ == "__main__":
    main()
