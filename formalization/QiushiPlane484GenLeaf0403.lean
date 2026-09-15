import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0403Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 121, .occ 124, .occ 130, .occ 137, .occ 141, .occ 325, .occ 509, .occ 690, .occ 1145, .occ 1161, .occ 1164, .occ 1168, .occ 1174, .occ 1180, .occ 1191, .occ 1196, .occ 1216, .occ 1237, .occ 1357, .occ 1370, .occ 1375, .occ 1486, .occ 1532, .occ 1533, .occ 1571, .occ 1607, .occ 1664, .sumGe, .nonneg 8, .nonneg 10, .nonneg 12, .branchLe 15 (0), .branchGe 2 (1), .branchGe 7 (1), .branchLe 6 (0), .branchLe 31 (0), .branchLe 24 (0), .branchGe 37 (1), .branchGe 0 (1), .branchLe 5 (0), .branchLe 1 (0), .branchGe 33 (1), .branchLe 14 (0)]

def plane484GenLeaf0403Mult : Fin 44 → Nat := ![3719, 2335, 1546, 119, 1490, 1969, 155, 520, 1116, 129, 1697, 957, 911, 1961, 303, 1348, 2714, 269, 660, 119, 119, 1048, 2851, 142, 411, 753, 2155, 776, 6949, 658, 2333, 1100, 6018, 4340, 15599, 6949, 6830, 1920, 5413, 5742, 1219, 2653, 3063, 6830]

theorem plane484GenLeaf0403 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_33 : (1 : Int) ≤ x 33)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0403Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0403Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0403Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0403Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 124
  · exact hroot.hOcc 130
  · exact hroot.hOcc 137
  · exact hroot.hOcc 141
  · exact hroot.hOcc 325
  · exact hroot.hOcc 509
  · exact hroot.hOcc 690
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1161
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1180
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1237
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1370
  · exact hroot.hOcc 1375
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1532
  · exact hroot.hOcc 1533
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1664
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (12 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (31 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (33 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_33
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14

end QiushiMatmul
