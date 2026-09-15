import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0362Refs : Fin 44 → RowRef 1665 43 := ![.occ 122, .occ 123, .occ 125, .occ 132, .occ 136, .occ 137, .occ 138, .occ 258, .occ 287, .occ 496, .occ 627, .occ 685, .occ 1109, .occ 1115, .occ 1143, .occ 1169, .occ 1187, .occ 1213, .occ 1228, .occ 1369, .occ 1399, .occ 1441, .occ 1457, .occ 1471, .occ 1480, .occ 1491, .occ 1526, .occ 1537, .occ 1580, .occ 1601, .occ 1606, .occ 1660, .sumGe, .nonneg 25, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchGe 23 (1), .branchLe 35 (0), .branchLe 3 (0), .branchGe 24 (1), .branchLe 40 (0), .branchGe 34 (1), .branchLe 27 (0)]

def plane484GenLeaf0362Mult : Fin 44 → Nat := ![101882, 36253, 39764, 100912, 52255, 106633, 62497, 27885, 22131, 36972, 40154, 21426, 11452, 247, 98105, 20610, 6426, 61418, 26810, 26311, 8932, 8350, 4532, 3862, 28508, 41274, 12709, 2564, 90670, 46104, 20468, 74023, 262364, 23728, 97336, 220803, 262364, 287003, 180478, 157780, 398361, 258502, 181010, 262364]

theorem plane484GenLeaf0362 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hUB_40 : x 40 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0362Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0362Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0362Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0362Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 125
  · exact hroot.hOcc 132
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 258
  · exact hroot.hOcc 287
  · exact hroot.hOcc 496
  · exact hroot.hOcc 627
  · exact hroot.hOcc 685
  · exact hroot.hOcc 1109
  · exact hroot.hOcc 1115
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1169
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1228
  · exact hroot.hOcc 1369
  · exact hroot.hOcc 1399
  · exact hroot.hOcc 1441
  · exact hroot.hOcc 1457
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1480
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1526
  · exact hroot.hOcc 1537
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1660
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24
  · change (∑ k, (if k = (40 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (27 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27

end QiushiMatmul
