#!/usr/bin/env python3
r"""analysis: verify the induced E11 stabilizer preserves the complete core Wang table.

The transported overlap cuts from the analysis radius-3 proof are valid only for
whole-support images under automorphisms of the E11 quotient Wang occupation
system.  This script supplies the missing computational certificate:

* generate the same 1152 point permutations used for transported centers;
* check they are F2-linear maps on the 8 quotient coordinates;
* find a small generating set whose closure is exactly these 1152 permutations;
* for each generator, verify over all 417,199 E11-core subspace rows that
  key -> g(key) is a bijection of the table and L(gU)=L(U).

Generator-level preservation plus generated closure size 1152 proves every
listed transported center is a whole-support image under a table-preserving
map.  This is still a computational correspondence certificate, not a tensor
rank lower bound.
"""
from __future__ import annotations

import json
import pickle
import sys
import time
from collections import Counter, deque
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

SCRIPTS = Path(__file__).resolve().parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from core_capacity_from_wang_lut import CoreQuotient  # noqa: E402
from complete_core_and_transversal import ROOT, build_core_constraints  # noqa: E402
from distinct_trace_cut_cpsat import generate_stabilizer_permutations  # noqa: E402
from wang_capacity_lazy import pack_basis, rref_basis, unpack_basis  # noqa: E402

OUTDIR = ROOT / "workspace/data/transported_overlap"
BASE_SUPPORT = [1,2,3,4,8,20,24,31,32,36,64,73,109,127,128,141,160,182,219]


def load_full_lut(path: Path):
    with path.open("rb") as f:
        payload = pickle.load(f)
    return {int(k): int(v) for k, v in payload["lut"].items()}, payload.get("meta", {})


def transform8(v: int, basis_images: Sequence[int]) -> int:
    out = 0
    x = int(v)
    bit = 0
    while x:
        if x & 1:
            out ^= int(basis_images[bit])
        bit += 1
        x >>= 1
    return out


def basis_images_from_perm(perm: Sequence[int]) -> Tuple[int, ...]:
    return tuple(int(perm[1 << i]) for i in range(8))


def is_linear_perm(perm: Sequence[int]) -> Tuple[bool, str]:
    imgs = basis_images_from_perm(perm)
    if len(set(imgs)) != 8 or any(z == 0 for z in imgs):
        return False, "basis image degeneracy"
    for p in range(256):
        if transform8(p, imgs) != int(perm[p]):
            return False, f"nonlinear at {p}: expected {perm[p]} got {transform8(p, imgs)}"
    return True, "ok"


def transform_key8(key8: int, basis_images: Sequence[int]) -> int:
    rows = unpack_basis(int(key8))
    return pack_basis(rref_basis((transform8(r, basis_images) for r in rows), n=8))


def compose(g: Tuple[int, ...], h: Tuple[int, ...]) -> Tuple[int, ...]:
    """Return g∘h, with point maps stored as perm[p]."""
    return tuple(g[h[i]] for i in range(256))


def close_group(gens: Sequence[Tuple[int, ...]]) -> set[Tuple[int, ...]]:
    ident = tuple(range(256))
    group: set[Tuple[int, ...]] = {ident}
    q: deque[Tuple[int, ...]] = deque()
    for g in gens:
        if g not in group:
            group.add(g)
            q.append(g)
    while q:
        a = q.popleft()
        snapshot = list(group)
        for b in snapshot:
            for c in (compose(a, b), compose(b, a)):
                if c not in group:
                    group.add(c)
                    q.append(c)
    return group


def greedy_generators(perms: Sequence[Tuple[int, ...]]) -> Tuple[List[Tuple[int, ...]], set[Tuple[int, ...]], List[dict]]:
    target = set(perms)
    ident = tuple(range(256))
    gens: List[Tuple[int, ...]] = []
    group: set[Tuple[int, ...]] = {ident}
    history = []
    candidates = [p for p in sorted(target) if p != ident]
    while len(group) < len(target):
        chosen = None
        best_group = None
        best_size = len(group)
        # Search for a candidate that grows the current group substantially.
        for cand in candidates:
            if cand in group:
                continue
            trial = close_group(gens + [cand])
            if not trial <= target:
                raise RuntimeError("generated permutation outside target enumeration")
            if len(trial) > best_size:
                chosen = cand
                best_group = trial
                best_size = len(trial)
                # A strong enough growth is fine; avoid testing every remaining candidate every time.
                if best_size >= 2 * max(1, len(group)) or best_size == len(target):
                    break
        if chosen is None or best_group is None:
            raise RuntimeError(f"failed to grow group from size {len(group)} toward {len(target)}")
        gens.append(chosen)
        group = best_group
        history.append({"generator_index": len(gens) - 1, "closure_size": len(group)})
    return gens, group, history


def support_image(A: Sequence[int], perm: Sequence[int]) -> Tuple[int, ...]:
    return tuple(sorted(int(perm[p]) for p in A))


def main() -> None:
    t0 = time.time()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    perms_raw = generate_stabilizer_permutations(include_transpose=True)
    perms = [tuple(int(x) for x in p) for p in perms_raw]
    ident = tuple(range(256))
    perm_count = len(perms)
    unique_perm_count = len(set(perms))

    linear_failures = []
    matrix_records = []
    for idx, perm in enumerate(perms):
        ok, msg = is_linear_perm(perm)
        if not ok:
            linear_failures.append({"perm_index": idx, "message": msg})
            if len(linear_failures) >= 10:
                break
        imgs = basis_images_from_perm(perm)
        matrix_records.append({
            "perm_index": idx,
            "basis_images_decimal": list(imgs),
            "basis_images_binary": [format(z, "08b") for z in imgs],
        })
    if linear_failures:
        result = {"schema": "wang_invariance_check_v1", "linear_failures": linear_failures}
        out = OUTDIR / "wang_invariance_check.json"
        out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
        print(json.dumps(result, indent=2, sort_keys=True))
        return

    gens, closure, gen_history = greedy_generators(perms)
    if closure != set(perms):
        raise RuntimeError("generator closure did not equal enumerated permutation set")

    full_lut, full_meta = load_full_lut(ROOT / "workspace/data/wang_f2_lb20/wang_subspace_lut.pkl")
    core = CoreQuotient(1)
    records, core_meta = build_core_constraints(core, full_lut)
    L_by_key = {int(r["key8"]): int(r["L"]) for r in records}
    if len(L_by_key) != len(records):
        raise RuntimeError("duplicate core keys in records")
    all_keys = set(L_by_key)

    gen_checks = []
    any_mismatch = False
    for gi, g in enumerate(gens):
        imgs = basis_images_from_perm(g)
        image_keys = set()
        mismatch_head = []
        dim_hist = Counter()
        for key, L in L_by_key.items():
            k2 = transform_key8(key, imgs)
            image_keys.add(k2)
            dim_hist[key & 0xF] += 1
            L2 = L_by_key.get(k2)
            if L2 != L:
                any_mismatch = True
                if len(mismatch_head) < 20:
                    mismatch_head.append({"key8": int(key), "image_key8": int(k2), "L": int(L), "image_L": None if L2 is None else int(L2), "dim8": int(key & 0xF), "image_dim8": int(k2 & 0xF)})
        missing = len(all_keys - image_keys)
        extra = len(image_keys - all_keys)
        check = {
            "generator_index": gi,
            "basis_images_decimal": list(imgs),
            "basis_images_binary": [format(z, "08b") for z in imgs],
            "row_count_checked": len(L_by_key),
            "image_key_count": len(image_keys),
            "missing_image_keys": missing,
            "extra_image_keys": extra,
            "L_mismatch_count_head_only": len(mismatch_head),
            "mismatch_head": mismatch_head,
            "dim_hist_checked": {str(k): int(v) for k, v in sorted(dim_hist.items())},
            "passed": (missing == 0 and extra == 0 and not mismatch_head),
        }
        gen_checks.append(check)

    centers = {support_image(BASE_SUPPORT, p) for p in perms}
    base_stab = sum(1 for p in perms if support_image(BASE_SUPPORT, p) == tuple(sorted(BASE_SUPPORT)))
    result = {
        "schema": "wang_invariance_check_v1",
        "field": "F2",
        "core": "E11 quotient core",
        "purpose": "certify that transported analysis overlap cuts use whole-support images under complete-core-Wang-table-preserving linear maps",
        "permutation_count": perm_count,
        "unique_permutation_count": unique_perm_count,
        "all_permutations_linear_on_F2_8": True,
        "generator_count": len(gens),
        "generator_closure_size": len(closure),
        "generator_history": gen_history,
        "generator_checks": gen_checks,
        "all_generator_checks_passed": all(c["passed"] for c in gen_checks) and not any_mismatch,
        "complete_core_table": {
            "row_count": len(L_by_key),
            "meta": core_meta,
            "full_lut_meta_brief": {"subspace_count": full_meta.get("subspace_count") or full_meta.get("expected_subspace_count"), "coverage_ok": full_meta.get("coverage_ok"), "conflict_count": full_meta.get("conflict_count")},
        },
        "base_support": BASE_SUPPORT,
        "base_support_stabilizer_size_in_enumerated_group": base_stab,
        "unique_whole_support_image_count": len(centers),
        "consequence_if_true": "For every complete-Wang-admissible distinct 19-support X and every enumerated group element g, the analysis d=3 DRAT exclusion gives |X∩gS|<=15.",
        "scope_warning": "This validates the transported A-support occupation cuts for the enumerated E11 table-preserving group; it does not prove E11-core infeasibility, B/C completion, or characteristic-zero statements.",
        "permutation_basis_images_head": matrix_records[:20],
        "elapsed_sec": round(time.time() - t0, 3),
    }
    out = OUTDIR / "wang_invariance_check.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "out": str(out),
        "permutation_count": perm_count,
        "unique_permutation_count": unique_perm_count,
        "generator_count": len(gens),
        "generator_closure_size": len(closure),
        "all_generator_checks_passed": result["all_generator_checks_passed"],
        "unique_whole_support_image_count": len(centers),
        "elapsed_sec": result["elapsed_sec"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
