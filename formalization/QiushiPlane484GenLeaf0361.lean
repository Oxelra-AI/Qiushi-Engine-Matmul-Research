import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0361Refs : Fin 44 → RowRef 1665 43 := ![.occ 124, .occ 125, .occ 127, .occ 131, .occ 132, .occ 133, .occ 134, .occ 136, .occ 138, .occ 317, .occ 345, .occ 386, .occ 1146, .occ 1164, .occ 1183, .occ 1186, .occ 1215, .occ 1329, .occ 1459, .occ 1462, .occ 1491, .occ 1501, .occ 1503, .occ 1560, .occ 1580, .occ 1606, .occ 1621, .occ 1645, .occ 1655, .occ 1661, .sumGe, .nonneg 0, .nonneg 7, .nonneg 16, .nonneg 22, .nonneg 25, .branchLe 15 (0), .branchGe 2 (1), .branchGe 23 (1), .branchLe 35 (0), .branchLe 3 (0), .branchGe 24 (1), .branchLe 40 (0), .branchLe 34 (0)]

def plane484GenLeaf0361Mult : Fin 44 → Nat := ![97, 99, 42, 67, 77, 5, 25, 49, 88, 34, 2, 65, 4, 76, 19, 5, 30, 2, 67, 19, 92, 42, 14, 2, 34, 60, 26, 16, 18, 2, 240, 68, 20, 10, 24, 32, 34, 294, 418, 180, 106, 326, 206, 240]

theorem plane484GenLeaf0361 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hUB_40 : x 40 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0361Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0361Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0361Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0361Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 124
  · exact hroot.hOcc 125
  · exact hroot.hOcc 127
  · exact hroot.hOcc 131
  · exact hroot.hOcc 132
  · exact hroot.hOcc 133
  · exact hroot.hOcc 134
  · exact hroot.hOcc 136
  · exact hroot.hOcc 138
  · exact hroot.hOcc 317
  · exact hroot.hOcc 345
  · exact hroot.hOcc 386
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1329
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1501
  · exact hroot.hOcc 1503
  · exact hroot.hOcc 1560
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1621
  · exact hroot.hOcc 1645
  · exact hroot.hOcc 1655
  · exact hroot.hOcc 1661
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24
  · change (∑ k, (if k = (40 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34

end QiushiMatmul
