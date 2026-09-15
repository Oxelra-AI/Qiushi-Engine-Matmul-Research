import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0041Refs : Fin 49 → RowRef 668 48 := ![.occ 83, .occ 111, .occ 137, .occ 139, .occ 144, .occ 185, .occ 195, .occ 219, .occ 223, .occ 225, .occ 241, .occ 253, .occ 257, .occ 273, .occ 288, .occ 302, .occ 303, .occ 304, .occ 313, .occ 315, .occ 329, .occ 335, .occ 337, .occ 340, .occ 377, .occ 386, .occ 387, .occ 390, .occ 399, .occ 461, .occ 477, .occ 479, .occ 538, .occ 539, .occ 623, .occ 636, .occ 639, .occ 651, .occ 660, .occ 666, .sumGe, .nonneg 7, .nonneg 28, .nonneg 44, .branchLe 39 (0), .branchGe 23 (1), .branchLe 2 (0), .branchGe 4 (1), .branchLe 10 (0)]

def plane487GenLeaf0041Mult : Fin 49 → Nat := ![22528, 9934, 28226, 34750, 2328, 50696, 36372, 20966, 56, 26688, 38572, 2320, 2988, 4366, 31562, 2608, 20727, 10032, 6928, 32559, 372, 43730, 18862, 2310, 5860, 33819, 732, 2112, 3365, 1992, 19912, 3242, 6642, 11784, 14110, 27126, 1309, 24104, 5952, 1697, 89590, 16694, 9750, 11914, 86348, 349426, 36434, 141786, 63726]

theorem plane487GenLeaf0041 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0041Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0041Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0041Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0041Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 83
  · exact hroot.hOcc 111
  · exact hroot.hOcc 137
  · exact hroot.hOcc 139
  · exact hroot.hOcc 144
  · exact hroot.hOcc 185
  · exact hroot.hOcc 195
  · exact hroot.hOcc 219
  · exact hroot.hOcc 223
  · exact hroot.hOcc 225
  · exact hroot.hOcc 241
  · exact hroot.hOcc 253
  · exact hroot.hOcc 257
  · exact hroot.hOcc 273
  · exact hroot.hOcc 288
  · exact hroot.hOcc 302
  · exact hroot.hOcc 303
  · exact hroot.hOcc 304
  · exact hroot.hOcc 313
  · exact hroot.hOcc 315
  · exact hroot.hOcc 329
  · exact hroot.hOcc 335
  · exact hroot.hOcc 337
  · exact hroot.hOcc 340
  · exact hroot.hOcc 377
  · exact hroot.hOcc 386
  · exact hroot.hOcc 387
  · exact hroot.hOcc 390
  · exact hroot.hOcc 399
  · exact hroot.hOcc 461
  · exact hroot.hOcc 477
  · exact hroot.hOcc 479
  · exact hroot.hOcc 538
  · exact hroot.hOcc 539
  · exact hroot.hOcc 623
  · exact hroot.hOcc 636
  · exact hroot.hOcc 639
  · exact hroot.hOcc 651
  · exact hroot.hOcc 660
  · exact hroot.hOcc 666
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (28 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (44 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (2 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (4 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (10 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10

end QiushiMatmul
