import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0113Refs : Fin 38 → RowRef 726 49 := ![.occ 78, .occ 98, .occ 112, .occ 115, .occ 131, .occ 175, .occ 198, .occ 208, .occ 221, .occ 230, .occ 231, .occ 241, .occ 258, .occ 275, .occ 295, .occ 299, .occ 318, .occ 327, .occ 332, .occ 334, .occ 393, .occ 404, .occ 515, .occ 568, .occ 607, .occ 611, .occ 691, .occ 700, .occ 720, .sumGe, .nonneg 8, .nonneg 18, .nonneg 37, .branchGe 31 (1), .branchGe 44 (1), .branchGe 6 (1), .branchLe 15 (0), .branchGe 9 (1)]

def plane491GenLeaf0113Mult : Fin 38 → Nat := ![1, 6, 4, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 5, 6, 1, 1, 2, 1, 3, 2, 1, 4, 4, 2, 1, 1, 1, 1, 7, 2, 1, 1, 18, 27, 18, 7, 24]

theorem plane491GenLeaf0113 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_44 : (1 : Int) ≤ x 44)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hUB_15 : x 15 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0113Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0113Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0113Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0113Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 78
  · exact hroot.hOcc 98
  · exact hroot.hOcc 112
  · exact hroot.hOcc 115
  · exact hroot.hOcc 131
  · exact hroot.hOcc 175
  · exact hroot.hOcc 198
  · exact hroot.hOcc 208
  · exact hroot.hOcc 221
  · exact hroot.hOcc 230
  · exact hroot.hOcc 231
  · exact hroot.hOcc 241
  · exact hroot.hOcc 258
  · exact hroot.hOcc 275
  · exact hroot.hOcc 295
  · exact hroot.hOcc 299
  · exact hroot.hOcc 318
  · exact hroot.hOcc 327
  · exact hroot.hOcc 332
  · exact hroot.hOcc 334
  · exact hroot.hOcc 393
  · exact hroot.hOcc 404
  · exact hroot.hOcc 515
  · exact hroot.hOcc 568
  · exact hroot.hOcc 607
  · exact hroot.hOcc 611
  · exact hroot.hOcc 691
  · exact hroot.hOcc 700
  · exact hroot.hOcc 720
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (18 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (37 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_44
  · change (∑ k, (if k = (6 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (15 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (9 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9

end QiushiMatmul
