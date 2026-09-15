import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0426Refs : Fin 37 → RowRef 1665 43 := ![.occ 126, .occ 127, .occ 129, .occ 135, .occ 136, .occ 137, .occ 416, .occ 597, .occ 799, .occ 1012, .occ 1147, .occ 1174, .occ 1183, .occ 1208, .occ 1294, .occ 1325, .occ 1400, .occ 1407, .occ 1444, .occ 1445, .occ 1486, .occ 1491, .occ 1492, .occ 1509, .occ 1510, .occ 1571, .occ 1647, .occ 1653, .sumGe, .nonneg 3, .nonneg 10, .nonneg 14, .branchLe 15 (0), .branchGe 2 (1), .branchGe 7 (1), .branchGe 6 (1), .branchLe 33 (0)]

def plane484GenLeaf0426Mult : Fin 37 → Nat := ![50, 46, 60, 7, 12, 25, 3, 13, 5, 4, 22, 5, 18, 6, 4, 2, 1, 8, 6, 1, 17, 14, 8, 7, 7, 9, 9, 3, 60, 43, 44, 136, 53, 131, 215, 189, 60]

theorem plane484GenLeaf0426 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0426Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0426Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0426Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0426Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 126
  · exact hroot.hOcc 127
  · exact hroot.hOcc 129
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 416
  · exact hroot.hOcc 597
  · exact hroot.hOcc 799
  · exact hroot.hOcc 1012
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1294
  · exact hroot.hOcc 1325
  · exact hroot.hOcc 1400
  · exact hroot.hOcc 1407
  · exact hroot.hOcc 1444
  · exact hroot.hOcc 1445
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1509
  · exact hroot.hOcc 1510
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1647
  · exact hroot.hOcc 1653
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (33 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33

end QiushiMatmul
