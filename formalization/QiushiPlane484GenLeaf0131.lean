import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0131Refs : Fin 44 → RowRef 1665 43 := ![.occ 93, .occ 134, .occ 141, .occ 147, .occ 148, .occ 164, .occ 187, .occ 615, .occ 701, .occ 708, .occ 721, .occ 861, .occ 1148, .occ 1151, .occ 1168, .occ 1172, .occ 1173, .occ 1215, .occ 1351, .occ 1372, .occ 1381, .occ 1404, .occ 1421, .occ 1471, .occ 1477, .occ 1519, .occ 1557, .occ 1607, .occ 1623, .occ 1625, .occ 1626, .occ 1651, .occ 1660, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 39 (0), .branchGe 32 (1), .branchLe 37 (0), .branchLe 3 (0), .branchLe 12 (0)]

def plane484GenLeaf0131Mult : Fin 44 → Nat := ![8504, 7974, 992, 3130, 9226, 3710, 3450, 3148, 1000, 1068, 4048, 2542, 1840, 3081, 6822, 5996, 654, 703, 1120, 2984, 9014, 4052, 784, 1839, 462, 4638, 3644, 144, 3834, 462, 207, 6619, 1733, 25060, 16708, 25060, 24384, 20428, 20014, 21310, 56526, 25060, 20632, 22658]

theorem plane484GenLeaf0131 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0131Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0131Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0131Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0131Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 93
  · exact hroot.hOcc 134
  · exact hroot.hOcc 141
  · exact hroot.hOcc 147
  · exact hroot.hOcc 148
  · exact hroot.hOcc 164
  · exact hroot.hOcc 187
  · exact hroot.hOcc 615
  · exact hroot.hOcc 701
  · exact hroot.hOcc 708
  · exact hroot.hOcc 721
  · exact hroot.hOcc 861
  · exact hroot.hOcc 1148
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1351
  · exact hroot.hOcc 1372
  · exact hroot.hOcc 1381
  · exact hroot.hOcc 1404
  · exact hroot.hOcc 1421
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1519
  · exact hroot.hOcc 1557
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1623
  · exact hroot.hOcc 1625
  · exact hroot.hOcc 1626
  · exact hroot.hOcc 1651
  · exact hroot.hOcc 1660
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (32 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32
  · change (∑ k, (if k = (37 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (12 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12

end QiushiMatmul
