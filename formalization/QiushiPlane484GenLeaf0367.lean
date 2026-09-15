import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0367Refs : Fin 42 → RowRef 1665 43 := ![.occ 121, .occ 123, .occ 124, .occ 125, .occ 128, .occ 131, .occ 132, .occ 137, .occ 138, .occ 205, .occ 364, .occ 417, .occ 418, .occ 657, .occ 690, .occ 851, .occ 1032, .occ 1143, .occ 1144, .occ 1146, .occ 1147, .occ 1215, .occ 1281, .occ 1381, .occ 1383, .occ 1389, .occ 1491, .occ 1496, .occ 1580, .occ 1626, .sumGe, .nonneg 3, .nonneg 4, .nonneg 25, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchGe 23 (1), .branchLe 35 (0), .branchGe 24 (1), .branchGe 40 (1), .branchGe 5 (1)]

def plane484GenLeaf0367Mult : Fin 42 → Nat := ![735, 18, 611, 405, 611, 771, 503, 523, 557, 242, 110, 1194, 52, 390, 34, 482, 66, 1124, 34, 40, 40, 16, 52, 198, 148, 16, 866, 152, 18, 106, 1380, 930, 912, 610, 52, 2990, 34, 2680, 1228, 3622, 600, 5004]

theorem plane484GenLeaf0367 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_40 : (1 : Int) ≤ x 40)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0367Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0367Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0367Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0367Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 123
  · exact hroot.hOcc 124
  · exact hroot.hOcc 125
  · exact hroot.hOcc 128
  · exact hroot.hOcc 131
  · exact hroot.hOcc 132
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 205
  · exact hroot.hOcc 364
  · exact hroot.hOcc 417
  · exact hroot.hOcc 418
  · exact hroot.hOcc 657
  · exact hroot.hOcc 690
  · exact hroot.hOcc 851
  · exact hroot.hOcc 1032
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1144
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1281
  · exact hroot.hOcc 1381
  · exact hroot.hOcc 1383
  · exact hroot.hOcc 1389
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1626
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24
  · change (∑ k, (if k = (40 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_40
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5

end QiushiMatmul
