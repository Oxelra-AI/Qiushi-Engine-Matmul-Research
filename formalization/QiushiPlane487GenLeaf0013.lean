import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0013Refs : Fin 49 → RowRef 668 48 := ![.occ 83, .occ 87, .occ 118, .occ 119, .occ 216, .occ 231, .occ 235, .occ 239, .occ 246, .occ 268, .occ 303, .occ 312, .occ 315, .occ 316, .occ 322, .occ 343, .occ 354, .occ 381, .occ 386, .occ 390, .occ 399, .occ 400, .occ 408, .occ 427, .occ 459, .occ 468, .occ 509, .occ 521, .occ 546, .occ 566, .occ 568, .occ 626, .occ 639, .occ 651, .occ 654, .occ 656, .occ 660, .occ 664, .sumGe, .nonneg 7, .nonneg 31, .nonneg 46, .branchLe 39 (0), .branchLe 23 (0), .branchLe 6 (0), .branchLe 25 (0), .branchGe 12 (1), .branchLe 3 (0), .branchGe 24 (1)]

def plane487GenLeaf0013Mult : Fin 49 → Nat := ![210, 265, 1765, 343, 46, 178, 307, 17, 178, 319, 520, 437, 215, 289, 1160, 578, 746, 59, 1269, 150, 114, 151, 60, 220, 92, 280, 45, 210, 343, 944, 30, 35, 356, 30, 574, 788, 59, 154, 2517, 663, 322, 195, 1397, 2161, 2458, 524, 6076, 895, 6144]

theorem plane487GenLeaf0013 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0013Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0013Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0013Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0013Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 83
  · exact hroot.hOcc 87
  · exact hroot.hOcc 118
  · exact hroot.hOcc 119
  · exact hroot.hOcc 216
  · exact hroot.hOcc 231
  · exact hroot.hOcc 235
  · exact hroot.hOcc 239
  · exact hroot.hOcc 246
  · exact hroot.hOcc 268
  · exact hroot.hOcc 303
  · exact hroot.hOcc 312
  · exact hroot.hOcc 315
  · exact hroot.hOcc 316
  · exact hroot.hOcc 322
  · exact hroot.hOcc 343
  · exact hroot.hOcc 354
  · exact hroot.hOcc 381
  · exact hroot.hOcc 386
  · exact hroot.hOcc 390
  · exact hroot.hOcc 399
  · exact hroot.hOcc 400
  · exact hroot.hOcc 408
  · exact hroot.hOcc 427
  · exact hroot.hOcc 459
  · exact hroot.hOcc 468
  · exact hroot.hOcc 509
  · exact hroot.hOcc 521
  · exact hroot.hOcc 546
  · exact hroot.hOcc 566
  · exact hroot.hOcc 568
  · exact hroot.hOcc 626
  · exact hroot.hOcc 639
  · exact hroot.hOcc 651
  · exact hroot.hOcc 654
  · exact hroot.hOcc 656
  · exact hroot.hOcc 660
  · exact hroot.hOcc 664
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (31 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 31
  · change (∑ k, (if k = (46 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (6 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (25 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (12 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (3 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (24 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24

end QiushiMatmul
