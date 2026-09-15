import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0211Refs : Fin 44 → RowRef 1665 43 := ![.occ 135, .occ 139, .occ 141, .occ 220, .occ 230, .occ 383, .occ 438, .occ 465, .occ 828, .occ 860, .occ 981, .occ 1154, .occ 1160, .occ 1206, .occ 1234, .occ 1300, .occ 1306, .occ 1346, .occ 1373, .occ 1397, .occ 1439, .occ 1472, .occ 1488, .occ 1507, .occ 1516, .occ 1529, .occ 1603, .occ 1608, .occ 1623, .occ 1649, .occ 1653, .occ 1656, .sumGe, .nonneg 19, .nonneg 24, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchGe 35 (1), .branchLe 16 (0), .branchGe 18 (1), .branchLe 38 (0), .branchGe 37 (1), .branchGe 21 (1)]

def plane484GenLeaf0211Mult : Fin 44 → Nat := ![21, 2709, 2320, 4443, 398, 2855, 1514, 73, 786, 601, 674, 5, 759, 10, 2277, 545, 2447, 467, 1275, 1250, 494, 758, 504, 1527, 1376, 1163, 2520, 15, 1202, 1670, 493, 570, 6816, 743, 5433, 6291, 6291, 16779, 12468, 773, 18447, 6811, 5975, 17861]

theorem plane484GenLeaf0211 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0211Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0211Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0211Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0211Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 135
  · exact hroot.hOcc 139
  · exact hroot.hOcc 141
  · exact hroot.hOcc 220
  · exact hroot.hOcc 230
  · exact hroot.hOcc 383
  · exact hroot.hOcc 438
  · exact hroot.hOcc 465
  · exact hroot.hOcc 828
  · exact hroot.hOcc 860
  · exact hroot.hOcc 981
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1234
  · exact hroot.hOcc 1300
  · exact hroot.hOcc 1306
  · exact hroot.hOcc 1346
  · exact hroot.hOcc 1373
  · exact hroot.hOcc 1397
  · exact hroot.hOcc 1439
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1507
  · exact hroot.hOcc 1516
  · exact hroot.hOcc 1529
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1623
  · exact hroot.hOcc 1649
  · exact hroot.hOcc 1653
  · exact hroot.hOcc 1656
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (38 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21

end QiushiMatmul
