import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0489Refs : Fin 44 → RowRef 1665 43 := ![.occ 94, .occ 98, .occ 119, .occ 120, .occ 122, .occ 130, .occ 131, .occ 138, .occ 283, .occ 329, .occ 419, .occ 483, .occ 566, .occ 583, .occ 596, .occ 802, .occ 1145, .occ 1151, .occ 1159, .occ 1164, .occ 1168, .occ 1172, .occ 1245, .occ 1308, .occ 1590, .occ 1601, .occ 1609, .occ 1615, .occ 1658, .occ 1664, .sumGe, .nonneg 17, .nonneg 18, .nonneg 20, .nonneg 22, .nonneg 23, .nonneg 24, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchGe 0 (1), .branchGe 19 (1), .branchLe 28 (0), .branchLe 30 (0)]

def plane484GenLeaf0489Mult : Fin 44 → Nat := ![1425, 819, 233, 5525, 697, 3117, 6085, 10284, 945, 6431, 73, 497, 688, 372, 1173, 1499, 713, 1282, 1403, 1521, 713, 3036, 1446, 1446, 1394, 3899, 2090, 661, 248, 2848, 10997, 2058, 1377, 1835, 2323, 16420, 170, 20472, 9594, 4753, 20134, 25159, 10336, 10997]

theorem plane484GenLeaf0489 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0489Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0489Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0489Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0489Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 94
  · exact hroot.hOcc 98
  · exact hroot.hOcc 119
  · exact hroot.hOcc 120
  · exact hroot.hOcc 122
  · exact hroot.hOcc 130
  · exact hroot.hOcc 131
  · exact hroot.hOcc 138
  · exact hroot.hOcc 283
  · exact hroot.hOcc 329
  · exact hroot.hOcc 419
  · exact hroot.hOcc 483
  · exact hroot.hOcc 566
  · exact hroot.hOcc 583
  · exact hroot.hOcc 596
  · exact hroot.hOcc 802
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1159
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1245
  · exact hroot.hOcc 1308
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1658
  · exact hroot.hOcc 1664
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30

end QiushiMatmul
