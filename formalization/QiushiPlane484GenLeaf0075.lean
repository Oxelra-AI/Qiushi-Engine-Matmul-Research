import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0075Refs : Fin 34 → RowRef 1665 43 := ![.occ 479, .occ 482, .occ 491, .occ 602, .occ 719, .occ 738, .occ 825, .occ 861, .occ 936, .occ 1215, .occ 1221, .occ 1261, .occ 1305, .occ 1342, .occ 1384, .occ 1428, .occ 1437, .occ 1525, .occ 1562, .occ 1607, .occ 1608, .occ 1624, .occ 1644, .sumGe, .nonneg 6, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchGe 13 (1), .branchGe 42 (1), .branchLe 9 (0), .branchLe 20 (0), .branchGe 8 (1), .branchGe 28 (1)]

def plane484GenLeaf0075Mult : Fin 34 → Nat := ![9, 49, 4, 1, 47, 62, 13, 128, 13, 4, 12, 45, 60, 13, 22, 20, 4, 6, 20, 21, 65, 46, 20, 132, 62, 132, 112, 128, 159, 109, 112, 112, 346, 424]

theorem plane484GenLeaf0075 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0075Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0075Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0075Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0075Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 479
  · exact hroot.hOcc 482
  · exact hroot.hOcc 491
  · exact hroot.hOcc 602
  · exact hroot.hOcc 719
  · exact hroot.hOcc 738
  · exact hroot.hOcc 825
  · exact hroot.hOcc 861
  · exact hroot.hOcc 936
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1221
  · exact hroot.hOcc 1261
  · exact hroot.hOcc 1305
  · exact hroot.hOcc 1342
  · exact hroot.hOcc 1384
  · exact hroot.hOcc 1428
  · exact hroot.hOcc 1437
  · exact hroot.hOcc 1525
  · exact hroot.hOcc 1562
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1624
  · exact hroot.hOcc 1644
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42
  · change (∑ k, (if k = (9 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28

end QiushiMatmul
