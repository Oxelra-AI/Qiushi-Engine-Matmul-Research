import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0515Refs : Fin 42 → RowRef 1665 43 := ![.occ 119, .occ 122, .occ 123, .occ 125, .occ 128, .occ 129, .occ 131, .occ 138, .occ 216, .occ 220, .occ 230, .occ 388, .occ 593, .occ 595, .occ 840, .occ 1221, .occ 1234, .occ 1280, .occ 1303, .occ 1470, .occ 1514, .occ 1521, .occ 1527, .occ 1528, .occ 1531, .occ 1533, .occ 1546, .occ 1571, .occ 1590, .occ 1640, .occ 1649, .sumGe, .nonneg 1, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchLe 26 (0), .branchLe 30 (0), .branchLe 34 (0), .branchGe 8 (1), .branchLe 42 (0), .branchLe 31 (0)]

def plane484GenLeaf0515Mult : Fin 42 → Nat := ![61, 91, 70, 18, 9, 47, 120, 80, 2, 48, 58, 12, 166, 122, 32, 8, 6, 6, 74, 84, 2, 6, 46, 54, 4, 4, 6, 20, 52, 40, 12, 228, 20, 368, 310, 118, 74, 228, 208, 740, 144, 158]

theorem plane484GenLeaf0515 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0515Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0515Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0515Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0515Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 125
  · exact hroot.hOcc 128
  · exact hroot.hOcc 129
  · exact hroot.hOcc 131
  · exact hroot.hOcc 138
  · exact hroot.hOcc 216
  · exact hroot.hOcc 220
  · exact hroot.hOcc 230
  · exact hroot.hOcc 388
  · exact hroot.hOcc 593
  · exact hroot.hOcc 595
  · exact hroot.hOcc 840
  · exact hroot.hOcc 1221
  · exact hroot.hOcc 1234
  · exact hroot.hOcc 1280
  · exact hroot.hOcc 1303
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1514
  · exact hroot.hOcc 1521
  · exact hroot.hOcc 1527
  · exact hroot.hOcc 1528
  · exact hroot.hOcc 1531
  · exact hroot.hOcc 1533
  · exact hroot.hOcc 1546
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1640
  · exact hroot.hOcc 1649
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (31 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31

end QiushiMatmul
