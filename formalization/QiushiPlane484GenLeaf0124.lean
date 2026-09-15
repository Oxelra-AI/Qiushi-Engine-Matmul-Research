import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0124Refs : Fin 43 → RowRef 1665 43 := ![.occ 128, .occ 130, .occ 134, .occ 139, .occ 159, .occ 480, .occ 1100, .occ 1101, .occ 1136, .occ 1154, .occ 1190, .occ 1203, .occ 1213, .occ 1215, .occ 1239, .occ 1262, .occ 1290, .occ 1353, .occ 1357, .occ 1467, .occ 1538, .occ 1542, .occ 1580, .occ 1590, .occ 1597, .occ 1608, .occ 1619, .occ 1620, .occ 1652, .sumGe, .nonneg 3, .nonneg 11, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 39 (0), .branchLe 32 (0), .branchGe 28 (1), .branchLe 6 (0), .branchLe 42 (0), .branchGe 1 (1)]

def plane484GenLeaf0124Mult : Fin 43 → Nat := ![20988, 7335, 23214, 20436, 2646, 1770, 10311, 13079, 2733, 8503, 2694, 8945, 6525, 11089, 144, 2907, 9408, 11403, 5874, 2232, 2379, 4266, 2907, 9496, 9495, 3006, 5721, 8589, 4086, 54972, 31782, 8670, 24492, 52278, 51586, 24489, 16704, 37929, 52065, 39075, 50886, 49734, 86023]

theorem plane484GenLeaf0124 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0124Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0124Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0124Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0124Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 128
  · exact hroot.hOcc 130
  · exact hroot.hOcc 134
  · exact hroot.hOcc 139
  · exact hroot.hOcc 159
  · exact hroot.hOcc 480
  · exact hroot.hOcc 1100
  · exact hroot.hOcc 1101
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1203
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1239
  · exact hroot.hOcc 1262
  · exact hroot.hOcc 1290
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1538
  · exact hroot.hOcc 1542
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1619
  · exact hroot.hOcc 1620
  · exact hroot.hOcc 1652
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (11 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1

end QiushiMatmul
