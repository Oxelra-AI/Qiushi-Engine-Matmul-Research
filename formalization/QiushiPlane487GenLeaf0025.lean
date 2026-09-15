import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0025Refs : Fin 48 → RowRef 668 48 := ![.occ 82, .occ 94, .occ 100, .occ 110, .occ 111, .occ 119, .occ 157, .occ 218, .occ 224, .occ 227, .occ 231, .occ 246, .occ 288, .occ 294, .occ 295, .occ 296, .occ 302, .occ 303, .occ 315, .occ 380, .occ 381, .occ 386, .occ 414, .occ 434, .occ 445, .occ 471, .occ 472, .occ 497, .occ 536, .occ 550, .occ 555, .occ 577, .occ 604, .occ 610, .occ 634, .occ 648, .occ 650, .occ 652, .sumGe, .nonneg 0, .nonneg 30, .branchLe 39 (0), .branchLe 23 (0), .branchGe 6 (1), .branchLe 33 (0), .branchLe 14 (0), .branchLe 29 (0), .branchGe 44 (1)]

def plane487GenLeaf0025Mult : Fin 48 → Nat := ![4796, 2881, 8034, 23229, 2458, 3327, 2915, 14812, 5313, 25711, 11003, 4731, 3597, 7413, 5833, 30787, 4632, 16550, 24591, 18181, 1541, 5821, 23141, 2357, 73, 9639, 11809, 15662, 20640, 1169, 13122, 1696, 14575, 7333, 7626, 739, 2902, 353, 62000, 21282, 16167, 47289, 33459, 106382, 30044, 30285, 61261, 139045]

theorem plane487GenLeaf0025 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_44 : (1 : Int) ≤ x 44)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0025Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0025Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0025Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0025Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 82
  · exact hroot.hOcc 94
  · exact hroot.hOcc 100
  · exact hroot.hOcc 110
  · exact hroot.hOcc 111
  · exact hroot.hOcc 119
  · exact hroot.hOcc 157
  · exact hroot.hOcc 218
  · exact hroot.hOcc 224
  · exact hroot.hOcc 227
  · exact hroot.hOcc 231
  · exact hroot.hOcc 246
  · exact hroot.hOcc 288
  · exact hroot.hOcc 294
  · exact hroot.hOcc 295
  · exact hroot.hOcc 296
  · exact hroot.hOcc 302
  · exact hroot.hOcc 303
  · exact hroot.hOcc 315
  · exact hroot.hOcc 380
  · exact hroot.hOcc 381
  · exact hroot.hOcc 386
  · exact hroot.hOcc 414
  · exact hroot.hOcc 434
  · exact hroot.hOcc 445
  · exact hroot.hOcc 471
  · exact hroot.hOcc 472
  · exact hroot.hOcc 497
  · exact hroot.hOcc 536
  · exact hroot.hOcc 550
  · exact hroot.hOcc 555
  · exact hroot.hOcc 577
  · exact hroot.hOcc 604
  · exact hroot.hOcc 610
  · exact hroot.hOcc 634
  · exact hroot.hOcc 648
  · exact hroot.hOcc 650
  · exact hroot.hOcc 652
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (30 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (6 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (33 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (14 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (29 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (44 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_44

end QiushiMatmul
