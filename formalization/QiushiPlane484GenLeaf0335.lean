import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0335Refs : Fin 43 → RowRef 1665 43 := ![.occ 90, .occ 256, .occ 289, .occ 322, .occ 346, .occ 366, .occ 385, .occ 411, .occ 452, .occ 558, .occ 592, .occ 757, .occ 836, .occ 855, .occ 1083, .occ 1140, .occ 1146, .occ 1154, .occ 1168, .occ 1186, .occ 1215, .occ 1220, .occ 1459, .occ 1483, .occ 1517, .occ 1541, .occ 1593, .occ 1607, .occ 1608, .occ 1643, .occ 1650, .sumGe, .branchLe 15 (0), .branchLe 7 (0), .branchLe 23 (0), .branchGe 26 (1), .branchLe 14 (0), .branchGe 1 (1), .branchGe 30 (1), .branchLe 36 (0), .branchGe 27 (1), .branchLe 17 (0), .branchGe 38 (1)]

def plane484GenLeaf0335Mult : Fin 43 → Nat := ![70, 55, 24, 6, 82, 58, 113, 30, 35, 9, 16, 136, 26, 69, 3, 97, 56, 26, 94, 13, 40, 3, 3, 16, 47, 57, 33, 26, 13, 15, 8, 194, 120, 131, 120, 827, 194, 126, 238, 100, 363, 132, 411]

theorem plane484GenLeaf0335 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0335Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0335Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0335Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0335Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 90
  · exact hroot.hOcc 256
  · exact hroot.hOcc 289
  · exact hroot.hOcc 322
  · exact hroot.hOcc 346
  · exact hroot.hOcc 366
  · exact hroot.hOcc 385
  · exact hroot.hOcc 411
  · exact hroot.hOcc 452
  · exact hroot.hOcc 558
  · exact hroot.hOcc 592
  · exact hroot.hOcc 757
  · exact hroot.hOcc 836
  · exact hroot.hOcc 855
  · exact hroot.hOcc 1083
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1517
  · exact hroot.hOcc 1541
  · exact hroot.hOcc 1593
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1643
  · exact hroot.hOcc 1650
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (27 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (38 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38

end QiushiMatmul
