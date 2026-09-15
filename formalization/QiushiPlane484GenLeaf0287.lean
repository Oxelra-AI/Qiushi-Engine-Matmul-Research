import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0287Refs : Fin 42 → RowRef 1665 43 := ![.occ 122, .occ 123, .occ 129, .occ 134, .occ 136, .occ 138, .occ 169, .occ 214, .occ 255, .occ 289, .occ 309, .occ 567, .occ 676, .occ 737, .occ 1101, .occ 1154, .occ 1172, .occ 1173, .occ 1187, .occ 1438, .occ 1477, .occ 1481, .occ 1499, .occ 1507, .occ 1516, .occ 1567, .occ 1583, .occ 1603, .occ 1623, .occ 1649, .sumGe, .nonneg 12, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchGe 29 (1), .branchLe 34 (0), .branchGe 13 (1), .branchLe 24 (0), .branchGe 22 (1)]

def plane484GenLeaf0287Mult : Fin 42 → Nat := ![2, 89, 9, 12, 97, 4, 7, 4, 20, 53, 6, 8, 2, 42, 7, 27, 13, 80, 9, 60, 3, 6, 3, 3, 18, 3, 67, 12, 9, 5, 123, 31, 119, 138, 42, 36, 110, 96, 120, 354, 8, 298]

theorem plane484GenLeaf0287 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0287Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0287Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0287Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0287Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 129
  · exact hroot.hOcc 134
  · exact hroot.hOcc 136
  · exact hroot.hOcc 138
  · exact hroot.hOcc 169
  · exact hroot.hOcc 214
  · exact hroot.hOcc 255
  · exact hroot.hOcc 289
  · exact hroot.hOcc 309
  · exact hroot.hOcc 567
  · exact hroot.hOcc 676
  · exact hroot.hOcc 737
  · exact hroot.hOcc 1101
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1438
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1499
  · exact hroot.hOcc 1507
  · exact hroot.hOcc 1516
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1583
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1623
  · exact hroot.hOcc 1649
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (12 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22

end QiushiMatmul
