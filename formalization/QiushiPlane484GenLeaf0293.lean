import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0293Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 123, .occ 126, .occ 127, .occ 129, .occ 139, .occ 174, .occ 414, .occ 552, .occ 796, .occ 1102, .occ 1143, .occ 1151, .occ 1159, .occ 1160, .occ 1179, .occ 1180, .occ 1186, .occ 1200, .occ 1324, .occ 1337, .occ 1405, .occ 1411, .occ 1478, .occ 1491, .occ 1542, .occ 1571, .occ 1602, .occ 1610, .occ 1650, .sumGe, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchGe 29 (1), .branchGe 34 (1), .branchLe 36 (0), .branchLe 22 (0), .branchLe 32 (0), .branchLe 17 (0), .branchLe 20 (0), .branchGe 6 (1)]

def plane484GenLeaf0293Mult : Fin 44 → Nat := ![31653, 49169, 11445, 13290, 8169, 20472, 9858, 54780, 16922, 12488, 13066, 10726, 5636, 20132, 7888, 490, 2348, 490, 1664, 34068, 6230, 8436, 7366, 20288, 19264, 2348, 4012, 2838, 30152, 40656, 100832, 44968, 11352, 980, 100342, 39704, 38938, 115980, 61436, 73694, 95196, 43430, 77706, 295314]

theorem plane484GenLeaf0293 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0293Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0293Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0293Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0293Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 123
  · exact hroot.hOcc 126
  · exact hroot.hOcc 127
  · exact hroot.hOcc 129
  · exact hroot.hOcc 139
  · exact hroot.hOcc 174
  · exact hroot.hOcc 414
  · exact hroot.hOcc 552
  · exact hroot.hOcc 796
  · exact hroot.hOcc 1102
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1159
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1180
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1324
  · exact hroot.hOcc 1337
  · exact hroot.hOcc 1405
  · exact hroot.hOcc 1411
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1542
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1650
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6

end QiushiMatmul
