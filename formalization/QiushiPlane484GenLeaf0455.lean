import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0455Refs : Fin 43 → RowRef 1665 43 := ![.occ 128, .occ 133, .occ 134, .occ 137, .occ 138, .occ 139, .occ 140, .occ 144, .occ 191, .occ 192, .occ 674, .occ 716, .occ 737, .occ 763, .occ 769, .occ 813, .occ 1139, .occ 1154, .occ 1188, .occ 1203, .occ 1215, .occ 1402, .occ 1409, .occ 1453, .occ 1471, .occ 1477, .occ 1484, .occ 1491, .occ 1567, .occ 1629, .occ 1631, .occ 1637, .occ 1656, .sumGe, .nonneg 8, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 0 (0), .branchGe 29 (1), .branchLe 27 (0), .branchGe 42 (1), .branchGe 1 (1)]

def plane484GenLeaf0455Mult : Fin 43 → Nat := ![232, 390, 1926, 1105, 797, 1849, 555, 552, 2328, 1410, 2738, 5224, 3676, 606, 8694, 4722, 170, 848, 116, 772, 258, 3396, 492, 2904, 384, 1620, 2998, 2210, 2196, 5028, 176, 800, 1182, 10222, 308, 27290, 7224, 9002, 10222, 36994, 8486, 32708, 5720]

theorem plane484GenLeaf0455 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0455Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0455Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0455Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0455Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 128
  · exact hroot.hOcc 133
  · exact hroot.hOcc 134
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 144
  · exact hroot.hOcc 191
  · exact hroot.hOcc 192
  · exact hroot.hOcc 674
  · exact hroot.hOcc 716
  · exact hroot.hOcc 737
  · exact hroot.hOcc 763
  · exact hroot.hOcc 769
  · exact hroot.hOcc 813
  · exact hroot.hOcc 1139
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1203
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1402
  · exact hroot.hOcc 1409
  · exact hroot.hOcc 1453
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1629
  · exact hroot.hOcc 1631
  · exact hroot.hOcc 1637
  · exact hroot.hOcc 1656
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (27 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1

end QiushiMatmul
