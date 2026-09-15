import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0534Refs : Fin 42 → RowRef 1665 43 := ![.occ 127, .occ 128, .occ 130, .occ 277, .occ 284, .occ 285, .occ 295, .occ 464, .occ 599, .occ 749, .occ 863, .occ 975, .occ 986, .occ 1103, .occ 1188, .occ 1272, .occ 1277, .occ 1292, .occ 1300, .occ 1310, .occ 1339, .occ 1391, .occ 1411, .occ 1422, .occ 1424, .occ 1481, .occ 1483, .occ 1484, .occ 1559, .occ 1621, .occ 1624, .sumGe, .nonneg 2, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchLe 26 (0), .branchGe 30 (1), .branchLe 1 (0), .branchLe 0 (0), .branchLe 19 (0), .branchGe 14 (1)]

def plane484GenLeaf0534Mult : Fin 42 → Nat := ![797, 42, 277, 337, 1300, 207, 952, 1351, 942, 309, 216, 886, 37, 127, 937, 141, 74, 113, 37, 362, 173, 2, 50, 1, 289, 414, 106, 180, 37, 199, 51, 1351, 286, 4596, 2818, 1351, 1351, 6847, 512, 697, 1065, 7720]

theorem plane484GenLeaf0534 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0534Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0534Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0534Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0534Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 127
  · exact hroot.hOcc 128
  · exact hroot.hOcc 130
  · exact hroot.hOcc 277
  · exact hroot.hOcc 284
  · exact hroot.hOcc 285
  · exact hroot.hOcc 295
  · exact hroot.hOcc 464
  · exact hroot.hOcc 599
  · exact hroot.hOcc 749
  · exact hroot.hOcc 863
  · exact hroot.hOcc 975
  · exact hroot.hOcc 986
  · exact hroot.hOcc 1103
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1272
  · exact hroot.hOcc 1277
  · exact hroot.hOcc 1292
  · exact hroot.hOcc 1300
  · exact hroot.hOcc 1310
  · exact hroot.hOcc 1339
  · exact hroot.hOcc 1391
  · exact hroot.hOcc 1411
  · exact hroot.hOcc 1422
  · exact hroot.hOcc 1424
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1559
  · exact hroot.hOcc 1621
  · exact hroot.hOcc 1624
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14

end QiushiMatmul
