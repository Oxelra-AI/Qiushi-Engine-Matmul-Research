import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0242Refs : Fin 41 → RowRef 1665 43 := ![.occ 85, .occ 123, .occ 128, .occ 130, .occ 143, .occ 204, .occ 290, .occ 335, .occ 418, .occ 455, .occ 689, .occ 823, .occ 858, .occ 860, .occ 1140, .occ 1154, .occ 1170, .occ 1173, .occ 1186, .occ 1187, .occ 1196, .occ 1220, .occ 1329, .occ 1478, .occ 1489, .occ 1556, .occ 1602, .occ 1645, .sumGe, .nonneg 19, .nonneg 21, .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchLe 29 (0), .branchLe 17 (0), .branchLe 16 (0), .branchGe 31 (1), .branchGe 20 (1), .branchLe 4 (0)]

def plane484GenLeaf0242Mult : Fin 41 → Nat := ![39, 4, 359, 3, 334, 70, 219, 114, 395, 14, 137, 676, 955, 174, 144, 98, 416, 43, 199, 156, 126, 131, 101, 401, 411, 73, 403, 86, 1215, 90, 406, 1056, 755, 1041, 1215, 973, 1215, 1041, 899, 3710, 811]

theorem plane484GenLeaf0242 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0242Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0242Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0242Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0242Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 85
  · exact hroot.hOcc 123
  · exact hroot.hOcc 128
  · exact hroot.hOcc 130
  · exact hroot.hOcc 143
  · exact hroot.hOcc 204
  · exact hroot.hOcc 290
  · exact hroot.hOcc 335
  · exact hroot.hOcc 418
  · exact hroot.hOcc 455
  · exact hroot.hOcc 689
  · exact hroot.hOcc 823
  · exact hroot.hOcc 858
  · exact hroot.hOcc 860
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1329
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1556
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1645
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (31 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4

end QiushiMatmul
