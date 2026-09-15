import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0466Refs : Fin 40 → RowRef 1665 43 := ![.occ 122, .occ 123, .occ 125, .occ 138, .occ 140, .occ 329, .occ 480, .occ 483, .occ 486, .occ 500, .occ 514, .occ 944, .occ 972, .occ 1203, .occ 1241, .occ 1251, .occ 1301, .occ 1307, .occ 1311, .occ 1318, .occ 1394, .occ 1453, .occ 1454, .occ 1470, .occ 1519, .occ 1521, .occ 1526, .occ 1528, .occ 1563, .occ 1652, .sumGe, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 0 (0), .branchGe 29 (1), .branchGe 27 (1), .branchGe 8 (1), .branchLe 30 (0), .branchGe 41 (1)]

def plane484GenLeaf0466Mult : Fin 40 → Nat := ![24, 415, 82, 316, 81, 45, 33, 617, 365, 45, 114, 102, 414, 28, 235, 20, 158, 78, 20, 138, 158, 184, 52, 419, 20, 78, 196, 23, 4, 216, 813, 1934, 555, 813, 813, 787, 857, 1912, 809, 1513]

theorem plane484GenLeaf0466 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_41 : (1 : Int) ≤ x 41)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0466Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0466Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0466Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0466Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 125
  · exact hroot.hOcc 138
  · exact hroot.hOcc 140
  · exact hroot.hOcc 329
  · exact hroot.hOcc 480
  · exact hroot.hOcc 483
  · exact hroot.hOcc 486
  · exact hroot.hOcc 500
  · exact hroot.hOcc 514
  · exact hroot.hOcc 944
  · exact hroot.hOcc 972
  · exact hroot.hOcc 1203
  · exact hroot.hOcc 1241
  · exact hroot.hOcc 1251
  · exact hroot.hOcc 1301
  · exact hroot.hOcc 1307
  · exact hroot.hOcc 1311
  · exact hroot.hOcc 1318
  · exact hroot.hOcc 1394
  · exact hroot.hOcc 1453
  · exact hroot.hOcc 1454
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1519
  · exact hroot.hOcc 1521
  · exact hroot.hOcc 1526
  · exact hroot.hOcc 1528
  · exact hroot.hOcc 1563
  · exact hroot.hOcc 1652
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (27 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (41 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_41

end QiushiMatmul
