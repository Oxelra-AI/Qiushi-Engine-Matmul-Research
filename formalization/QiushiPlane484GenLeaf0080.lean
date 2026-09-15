import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0080Refs : Fin 44 → RowRef 1665 43 := ![.occ 121, .occ 122, .occ 123, .occ 129, .occ 134, .occ 137, .occ 141, .occ 492, .occ 524, .occ 544, .occ 720, .occ 739, .occ 741, .occ 1170, .occ 1172, .occ 1173, .occ 1183, .occ 1307, .occ 1375, .occ 1398, .occ 1401, .occ 1403, .occ 1428, .occ 1434, .occ 1472, .occ 1477, .occ 1530, .occ 1531, .occ 1534, .occ 1602, .occ 1655, .occ 1657, .sumGe, .nonneg 0, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchGe 13 (1), .branchGe 42 (1), .branchLe 9 (0), .branchGe 20 (1), .branchGe 41 (1), .branchLe 24 (0)]

def plane484GenLeaf0080Mult : Fin 44 → Nat := ![1976, 1891, 3143, 1471, 4623, 1067, 3655, 1737, 666, 1505, 1475, 2448, 197, 2696, 3195, 1191, 3029, 2055, 1157, 3726, 1157, 499, 1311, 431, 1018, 426, 499, 499, 3314, 4445, 2011, 368, 12313, 4340, 11156, 5074, 12313, 9996, 14986, 5977, 6826, 24722, 16260, 11156]

theorem plane484GenLeaf0080 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_41 : (1 : Int) ≤ x 41)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0080Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0080Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0080Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0080Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 129
  · exact hroot.hOcc 134
  · exact hroot.hOcc 137
  · exact hroot.hOcc 141
  · exact hroot.hOcc 492
  · exact hroot.hOcc 524
  · exact hroot.hOcc 544
  · exact hroot.hOcc 720
  · exact hroot.hOcc 739
  · exact hroot.hOcc 741
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1307
  · exact hroot.hOcc 1375
  · exact hroot.hOcc 1398
  · exact hroot.hOcc 1401
  · exact hroot.hOcc 1403
  · exact hroot.hOcc 1428
  · exact hroot.hOcc 1434
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1530
  · exact hroot.hOcc 1531
  · exact hroot.hOcc 1534
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1655
  · exact hroot.hOcc 1657
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42
  · change (∑ k, (if k = (9 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20
  · change (∑ k, (if k = (41 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_41
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24

end QiushiMatmul
