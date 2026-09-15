import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0554Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 122, .occ 131, .occ 133, .occ 138, .occ 144, .occ 157, .occ 242, .occ 295, .occ 471, .occ 573, .occ 610, .occ 857, .occ 939, .occ 1068, .occ 1140, .occ 1158, .occ 1170, .occ 1200, .occ 1205, .occ 1208, .occ 1220, .occ 1234, .occ 1266, .occ 1280, .occ 1288, .occ 1357, .occ 1481, .occ 1484, .occ 1563, .occ 1580, .occ 1603, .occ 1663, .sumGe, .nonneg 8, .nonneg 17, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchLe 26 (0), .branchGe 30 (1), .branchGe 1 (1), .branchGe 11 (1), .branchGe 32 (1)]

def plane484GenLeaf0554Mult : Fin 44 → Nat := ![3, 41, 3, 48, 6, 39, 10, 7, 18, 37, 17, 2, 3, 9, 25, 10, 14, 16, 28, 10, 21, 11, 1, 18, 1, 19, 3, 46, 4, 7, 9, 10, 24, 84, 17, 44, 148, 147, 35, 35, 129, 94, 242, 186]

theorem plane484GenLeaf0554 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0554Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0554Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0554Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0554Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 122
  · exact hroot.hOcc 131
  · exact hroot.hOcc 133
  · exact hroot.hOcc 138
  · exact hroot.hOcc 144
  · exact hroot.hOcc 157
  · exact hroot.hOcc 242
  · exact hroot.hOcc 295
  · exact hroot.hOcc 471
  · exact hroot.hOcc 573
  · exact hroot.hOcc 610
  · exact hroot.hOcc 857
  · exact hroot.hOcc 939
  · exact hroot.hOcc 1068
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1234
  · exact hroot.hOcc 1266
  · exact hroot.hOcc 1280
  · exact hroot.hOcc 1288
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1563
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1663
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (11 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11
  · change (∑ k, (if k = (32 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32

end QiushiMatmul
