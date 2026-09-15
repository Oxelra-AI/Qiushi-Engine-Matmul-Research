import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0081Refs : Fin 44 → RowRef 713 43 := ![.occ 89, .occ 93, .occ 105, .occ 108, .occ 115, .occ 119, .occ 120, .occ 178, .occ 203, .occ 216, .occ 219, .occ 245, .occ 246, .occ 247, .occ 248, .occ 250, .occ 290, .occ 299, .occ 375, .occ 459, .occ 461, .occ 464, .occ 466, .occ 486, .occ 491, .occ 505, .occ 522, .occ 602, .occ 653, .occ 658, .occ 679, .occ 704, .sumGe, .nonneg 14, .branchGe 29 (1), .branchLe 18 (0), .branchLe 12 (0), .branchLe 22 (0), .branchGe 1 (1), .branchLe 42 (0), .branchLe 32 (0), .branchLe 8 (0), .branchLe 16 (0), .branchGe 2 (1)]

def plane490GenLeaf0081Mult : Fin 44 → Nat := ![834, 14452, 13652, 6000, 2222, 415, 2741, 8451, 9762, 3108, 1582, 4489, 451, 992, 1282, 2767, 2227, 2416, 8210, 264, 1891, 545, 2270, 3108, 525, 6713, 1484, 9955, 3182, 2711, 834, 864, 17634, 1068, 40210, 6195, 15218, 16378, 792, 17634, 17634, 15936, 7679, 32415]

theorem plane490GenLeaf0081 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0081Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0081Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0081Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0081Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 89
  · exact hroot.hOcc 93
  · exact hroot.hOcc 105
  · exact hroot.hOcc 108
  · exact hroot.hOcc 115
  · exact hroot.hOcc 119
  · exact hroot.hOcc 120
  · exact hroot.hOcc 178
  · exact hroot.hOcc 203
  · exact hroot.hOcc 216
  · exact hroot.hOcc 219
  · exact hroot.hOcc 245
  · exact hroot.hOcc 246
  · exact hroot.hOcc 247
  · exact hroot.hOcc 248
  · exact hroot.hOcc 250
  · exact hroot.hOcc 290
  · exact hroot.hOcc 299
  · exact hroot.hOcc 375
  · exact hroot.hOcc 459
  · exact hroot.hOcc 461
  · exact hroot.hOcc 464
  · exact hroot.hOcc 466
  · exact hroot.hOcc 486
  · exact hroot.hOcc 491
  · exact hroot.hOcc 505
  · exact hroot.hOcc 522
  · exact hroot.hOcc 602
  · exact hroot.hOcc 653
  · exact hroot.hOcc 658
  · exact hroot.hOcc 679
  · exact hroot.hOcc 704
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (12 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2

end QiushiMatmul
