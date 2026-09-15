import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0465Refs : Fin 44 → RowRef 1665 43 := ![.occ 122, .occ 123, .occ 131, .occ 133, .occ 136, .occ 156, .occ 180, .occ 298, .occ 316, .occ 446, .occ 448, .occ 596, .occ 868, .occ 927, .occ 972, .occ 1025, .occ 1175, .occ 1176, .occ 1192, .occ 1216, .occ 1269, .occ 1338, .occ 1386, .occ 1441, .occ 1453, .occ 1470, .occ 1471, .occ 1489, .occ 1567, .occ 1590, .occ 1615, .occ 1630, .occ 1646, .sumGe, .nonneg 1, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 0 (0), .branchGe 29 (1), .branchGe 27 (1), .branchGe 8 (1), .branchLe 30 (0), .branchLe 41 (0)]

def plane484GenLeaf0465Mult : Fin 44 → Nat := ![60, 491, 319, 57, 16, 163, 2, 536, 485, 19, 13, 267, 733, 241, 807, 2, 144, 222, 12, 14, 1, 1, 167, 1, 242, 356, 182, 30, 1, 1, 1, 60, 487, 1039, 43, 2721, 1039, 1038, 705, 2790, 53, 3661, 552, 1039]

theorem plane484GenLeaf0465 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_41 : x 41 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0465Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0465Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0465Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0465Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 131
  · exact hroot.hOcc 133
  · exact hroot.hOcc 136
  · exact hroot.hOcc 156
  · exact hroot.hOcc 180
  · exact hroot.hOcc 298
  · exact hroot.hOcc 316
  · exact hroot.hOcc 446
  · exact hroot.hOcc 448
  · exact hroot.hOcc 596
  · exact hroot.hOcc 868
  · exact hroot.hOcc 927
  · exact hroot.hOcc 972
  · exact hroot.hOcc 1025
  · exact hroot.hOcc 1175
  · exact hroot.hOcc 1176
  · exact hroot.hOcc 1192
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1269
  · exact hroot.hOcc 1338
  · exact hroot.hOcc 1386
  · exact hroot.hOcc 1441
  · exact hroot.hOcc 1453
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1630
  · exact hroot.hOcc 1646
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (27 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (41 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_41

end QiushiMatmul
