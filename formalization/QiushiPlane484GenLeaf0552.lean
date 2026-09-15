import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0552Refs : Fin 44 → RowRef 1665 43 := ![.occ 127, .occ 131, .occ 140, .occ 170, .occ 196, .occ 283, .occ 295, .occ 333, .occ 377, .occ 471, .occ 858, .occ 860, .occ 967, .occ 1154, .occ 1158, .occ 1160, .occ 1170, .occ 1173, .occ 1200, .occ 1208, .occ 1235, .occ 1418, .occ 1424, .occ 1472, .occ 1478, .occ 1484, .occ 1488, .occ 1539, .occ 1556, .occ 1623, .occ 1629, .occ 1651, .sumGe, .nonneg 16, .nonneg 24, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchLe 26 (0), .branchGe 30 (1), .branchGe 1 (1), .branchLe 11 (0), .branchGe 32 (1), .branchGe 20 (1)]

def plane484GenLeaf0552Mult : Fin 44 → Nat := ![7680, 13528, 25759, 11648, 1245, 2952, 4427, 17119, 11911, 8609, 8959, 1766, 6432, 1766, 8715, 732, 6337, 350, 5577, 8058, 7492, 3368, 1220, 7831, 151, 4570, 11891, 13737, 9917, 1335, 1966, 1205, 30997, 14807, 46883, 95697, 60276, 16971, 2698, 58668, 28137, 17878, 83037, 100985]

theorem plane484GenLeaf0552 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0552Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0552Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0552Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0552Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 127
  · exact hroot.hOcc 131
  · exact hroot.hOcc 140
  · exact hroot.hOcc 170
  · exact hroot.hOcc 196
  · exact hroot.hOcc 283
  · exact hroot.hOcc 295
  · exact hroot.hOcc 333
  · exact hroot.hOcc 377
  · exact hroot.hOcc 471
  · exact hroot.hOcc 858
  · exact hroot.hOcc 860
  · exact hroot.hOcc 967
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1235
  · exact hroot.hOcc 1418
  · exact hroot.hOcc 1424
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1539
  · exact hroot.hOcc 1556
  · exact hroot.hOcc 1623
  · exact hroot.hOcc 1629
  · exact hroot.hOcc 1651
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (11 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (32 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20

end QiushiMatmul
