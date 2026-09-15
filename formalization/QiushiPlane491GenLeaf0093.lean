import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0093Refs : Fin 27 → RowRef 726 49 := ![.occ 103, .occ 106, .occ 153, .occ 169, .occ 181, .occ 268, .occ 323, .occ 343, .occ 344, .occ 489, .occ 522, .occ 601, .occ 611, .occ 622, .occ 632, .occ 644, .occ 665, .occ 708, .sumGe, .nonneg 35, .branchGe 31 (1), .branchLe 44 (0), .branchGe 11 (1), .branchLe 7 (0), .branchGe 39 (1), .branchLe 8 (0), .branchGe 27 (1)]

def plane491GenLeaf0093Mult : Fin 27 → Nat := ![1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 10, 3, 5, 2, 10, 3, 15]

theorem plane491GenLeaf0093 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0093Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0093Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0093Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0093Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 103
  · exact hroot.hOcc 106
  · exact hroot.hOcc 153
  · exact hroot.hOcc 169
  · exact hroot.hOcc 181
  · exact hroot.hOcc 268
  · exact hroot.hOcc 323
  · exact hroot.hOcc 343
  · exact hroot.hOcc 344
  · exact hroot.hOcc 489
  · exact hroot.hOcc 522
  · exact hroot.hOcc 601
  · exact hroot.hOcc 611
  · exact hroot.hOcc 622
  · exact hroot.hOcc 632
  · exact hroot.hOcc 644
  · exact hroot.hOcc 665
  · exact hroot.hOcc 708
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (35 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 35
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (11 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11
  · change (∑ k, (if k = (7 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (39 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (8 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (27 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27

end QiushiMatmul
