import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0479Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 123, .occ 128, .occ 129, .occ 131, .occ 132, .occ 138, .occ 142, .occ 180, .occ 447, .occ 498, .occ 502, .occ 513, .occ 596, .occ 763, .occ 861, .occ 1136, .occ 1200, .occ 1256, .occ 1386, .occ 1436, .occ 1469, .occ 1471, .occ 1480, .occ 1569, .occ 1590, .occ 1600, .occ 1636, .occ 1659, .sumGe, .nonneg 20, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchGe 0 (1), .branchLe 19 (0), .branchLe 25 (0), .branchLe 3 (0), .branchGe 38 (1), .branchGe 34 (1), .branchLe 28 (0), .branchLe 32 (0), .branchLe 36 (0), .branchGe 8 (1)]

def plane484GenLeaf0479Mult : Fin 44 → Nat := ![280, 377, 247, 226, 396, 172, 184, 528, 135, 292, 104, 728, 52, 948, 44, 349, 188, 188, 68, 340, 112, 116, 4, 228, 20, 420, 104, 4, 184, 1136, 68, 2492, 1136, 206, 942, 452, 92, 44, 660, 1044, 1136, 1136, 944, 3030]

theorem plane484GenLeaf0479 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0479Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0479Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0479Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0479Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 123
  · exact hroot.hOcc 128
  · exact hroot.hOcc 129
  · exact hroot.hOcc 131
  · exact hroot.hOcc 132
  · exact hroot.hOcc 138
  · exact hroot.hOcc 142
  · exact hroot.hOcc 180
  · exact hroot.hOcc 447
  · exact hroot.hOcc 498
  · exact hroot.hOcc 502
  · exact hroot.hOcc 513
  · exact hroot.hOcc 596
  · exact hroot.hOcc 763
  · exact hroot.hOcc 861
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1256
  · exact hroot.hOcc 1386
  · exact hroot.hOcc 1436
  · exact hroot.hOcc 1469
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1480
  · exact hroot.hOcc 1569
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1600
  · exact hroot.hOcc 1636
  · exact hroot.hOcc 1659
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (38 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8

end QiushiMatmul
