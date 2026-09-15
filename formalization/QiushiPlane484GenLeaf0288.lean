import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0288Refs : Fin 44 → RowRef 1665 43 := ![.occ 123, .occ 124, .occ 129, .occ 130, .occ 135, .occ 136, .occ 201, .occ 321, .occ 449, .occ 470, .occ 478, .occ 567, .occ 604, .occ 615, .occ 737, .occ 1101, .occ 1140, .occ 1173, .occ 1190, .occ 1196, .occ 1214, .occ 1215, .occ 1327, .occ 1357, .occ 1481, .occ 1484, .occ 1486, .occ 1492, .occ 1529, .occ 1580, .occ 1582, .occ 1601, .sumGe, .nonneg 7, .nonneg 25, .branchLe 15 (0), .branchGe 2 (1), .branchLe 23 (0), .branchLe 26 (0), .branchGe 29 (1), .branchLe 34 (0), .branchGe 13 (1), .branchGe 24 (1), .branchLe 4 (0)]

def plane484GenLeaf0288Mult : Fin 44 → Nat := ![22387, 8429, 17399, 13223, 30984, 33790, 8412, 15260, 7862, 990, 3626, 158, 2058, 3066, 17930, 2784, 4616, 124, 3778, 7466, 508, 27976, 3224, 9254, 6856, 7590, 6052, 4638, 6008, 5464, 6300, 4582, 47648, 490, 21764, 9074, 84322, 35328, 7400, 54920, 42558, 93586, 113360, 25996]

theorem plane484GenLeaf0288 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0288Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0288Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0288Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0288Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 123
  · exact hroot.hOcc 124
  · exact hroot.hOcc 129
  · exact hroot.hOcc 130
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 201
  · exact hroot.hOcc 321
  · exact hroot.hOcc 449
  · exact hroot.hOcc 470
  · exact hroot.hOcc 478
  · exact hroot.hOcc 567
  · exact hroot.hOcc 604
  · exact hroot.hOcc 615
  · exact hroot.hOcc 737
  · exact hroot.hOcc 1101
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1327
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1529
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1582
  · exact hroot.hOcc 1601
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4

end QiushiMatmul
