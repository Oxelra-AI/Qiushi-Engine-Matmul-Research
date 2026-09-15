import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0089Refs : Fin 42 → RowRef 1665 43 := ![.occ 124, .occ 130, .occ 139, .occ 283, .occ 356, .occ 707, .occ 965, .occ 992, .occ 1244, .occ 1245, .occ 1256, .occ 1270, .occ 1369, .occ 1384, .occ 1435, .occ 1438, .occ 1441, .occ 1442, .occ 1444, .occ 1451, .occ 1518, .occ 1522, .occ 1541, .occ 1545, .occ 1609, .occ 1620, .occ 1628, .occ 1655, .occ 1661, .occ 1663, .sumGe, .nonneg 25, .nonneg 26, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchGe 4 (1), .branchLe 36 (0), .branchLe 24 (0), .branchGe 19 (1), .branchLe 6 (0), .branchGe 18 (1)]

def plane484GenLeaf0089Mult : Fin 42 → Nat := ![5, 1516, 10475, 1450, 1450, 8698, 1920, 3906, 121, 226, 2953, 4246, 421, 2204, 766, 138, 1208, 121, 7400, 1062, 524, 2987, 3564, 4745, 88, 7499, 4393, 2943, 662, 798, 19261, 1516, 31130, 19261, 19256, 19261, 20799, 18461, 242, 33854, 19173, 51841]

theorem plane484GenLeaf0089 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0089Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0089Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0089Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0089Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 124
  · exact hroot.hOcc 130
  · exact hroot.hOcc 139
  · exact hroot.hOcc 283
  · exact hroot.hOcc 356
  · exact hroot.hOcc 707
  · exact hroot.hOcc 965
  · exact hroot.hOcc 992
  · exact hroot.hOcc 1244
  · exact hroot.hOcc 1245
  · exact hroot.hOcc 1256
  · exact hroot.hOcc 1270
  · exact hroot.hOcc 1369
  · exact hroot.hOcc 1384
  · exact hroot.hOcc 1435
  · exact hroot.hOcc 1438
  · exact hroot.hOcc 1441
  · exact hroot.hOcc 1442
  · exact hroot.hOcc 1444
  · exact hroot.hOcc 1451
  · exact hroot.hOcc 1518
  · exact hroot.hOcc 1522
  · exact hroot.hOcc 1541
  · exact hroot.hOcc 1545
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1620
  · exact hroot.hOcc 1628
  · exact hroot.hOcc 1655
  · exact hroot.hOcc 1661
  · exact hroot.hOcc 1663
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18

end QiushiMatmul
