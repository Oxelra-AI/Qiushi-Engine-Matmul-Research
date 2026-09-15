import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0406Refs : Fin 38 → RowRef 1665 43 := ![.occ 119, .occ 121, .occ 127, .occ 129, .occ 134, .occ 141, .occ 143, .occ 213, .occ 386, .occ 442, .occ 509, .occ 598, .occ 1119, .occ 1164, .occ 1166, .occ 1174, .occ 1182, .occ 1196, .occ 1205, .occ 1206, .occ 1208, .occ 1408, .occ 1486, .occ 1531, .occ 1571, .occ 1607, .sumGe, .nonneg 10, .branchLe 15 (0), .branchGe 2 (1), .branchGe 7 (1), .branchLe 31 (0), .branchLe 24 (0), .branchGe 37 (1), .branchGe 0 (1), .branchGe 1 (1), .branchLe 21 (0), .branchGe 35 (1)]

def plane484GenLeaf0406Mult : Fin 38 → Nat := ![21, 47, 53, 9, 22, 28, 60, 12, 34, 44, 20, 12, 54, 18, 10, 20, 44, 32, 2, 2, 8, 6, 56, 18, 44, 66, 128, 166, 124, 196, 526, 128, 100, 156, 24, 26, 44, 160]

theorem plane484GenLeaf0406 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0406Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0406Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0406Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0406Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 127
  · exact hroot.hOcc 129
  · exact hroot.hOcc 134
  · exact hroot.hOcc 141
  · exact hroot.hOcc 143
  · exact hroot.hOcc 213
  · exact hroot.hOcc 386
  · exact hroot.hOcc 442
  · exact hroot.hOcc 509
  · exact hroot.hOcc 598
  · exact hroot.hOcc 1119
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1182
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1408
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1531
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1607
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (31 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (21 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35

end QiushiMatmul
