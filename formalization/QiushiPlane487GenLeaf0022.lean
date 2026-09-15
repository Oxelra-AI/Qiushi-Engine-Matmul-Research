import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0022Refs : Fin 48 → RowRef 668 48 := ![.occ 86, .occ 87, .occ 94, .occ 95, .occ 102, .occ 106, .occ 110, .occ 218, .occ 219, .occ 227, .occ 235, .occ 253, .occ 274, .occ 294, .occ 295, .occ 303, .occ 306, .occ 322, .occ 378, .occ 386, .occ 389, .occ 396, .occ 471, .occ 474, .occ 526, .occ 531, .occ 561, .occ 615, .occ 634, .occ 648, .occ 650, .occ 661, .occ 664, .sumGe, .nonneg 0, .nonneg 31, .nonneg 38, .nonneg 40, .branchLe 39 (0), .branchLe 23 (0), .branchGe 6 (1), .branchLe 33 (0), .branchLe 14 (0), .branchLe 29 (0), .branchLe 44 (0), .branchLe 25 (0), .branchLe 22 (0), .branchGe 41 (1)]

def plane487GenLeaf0022Mult : Fin 48 → Nat := ![56, 202, 19, 116, 273, 15, 223, 58, 291, 75, 56, 28, 59, 28, 188, 59, 169, 246, 395, 318, 12, 10, 256, 218, 28, 63, 48, 33, 41, 154, 188, 228, 28, 776, 218, 251, 226, 280, 304, 748, 1770, 776, 368, 313, 519, 275, 142, 1075]

theorem plane487GenLeaf0022 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_41 : (1 : Int) ≤ x 41)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0022Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0022Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0022Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0022Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 86
  · exact hroot.hOcc 87
  · exact hroot.hOcc 94
  · exact hroot.hOcc 95
  · exact hroot.hOcc 102
  · exact hroot.hOcc 106
  · exact hroot.hOcc 110
  · exact hroot.hOcc 218
  · exact hroot.hOcc 219
  · exact hroot.hOcc 227
  · exact hroot.hOcc 235
  · exact hroot.hOcc 253
  · exact hroot.hOcc 274
  · exact hroot.hOcc 294
  · exact hroot.hOcc 295
  · exact hroot.hOcc 303
  · exact hroot.hOcc 306
  · exact hroot.hOcc 322
  · exact hroot.hOcc 378
  · exact hroot.hOcc 386
  · exact hroot.hOcc 389
  · exact hroot.hOcc 396
  · exact hroot.hOcc 471
  · exact hroot.hOcc 474
  · exact hroot.hOcc 526
  · exact hroot.hOcc 531
  · exact hroot.hOcc 561
  · exact hroot.hOcc 615
  · exact hroot.hOcc 634
  · exact hroot.hOcc 648
  · exact hroot.hOcc 650
  · exact hroot.hOcc 661
  · exact hroot.hOcc 664
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (31 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 31
  · change (∑ k, (if k = (38 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (40 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (6 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (33 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (14 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (29 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (44 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (25 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (22 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (41 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_41

end QiushiMatmul
