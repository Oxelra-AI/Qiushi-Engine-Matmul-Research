import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0458Refs : Fin 42 → RowRef 1665 43 := ![.occ 133, .occ 135, .occ 138, .occ 191, .occ 283, .occ 412, .occ 514, .occ 545, .occ 584, .occ 674, .occ 1101, .occ 1140, .occ 1147, .occ 1188, .occ 1205, .occ 1206, .occ 1276, .occ 1285, .occ 1310, .occ 1402, .occ 1409, .occ 1462, .occ 1467, .occ 1484, .occ 1536, .occ 1580, .occ 1590, .occ 1641, .sumGe, .nonneg 7, .nonneg 17, .nonneg 24, .branchGe 15 (1), .branchLe 35 (0), .branchLe 0 (0), .branchGe 29 (1), .branchGe 27 (1), .branchLe 8 (0), .branchLe 4 (0), .branchLe 16 (0), .branchLe 22 (0), .branchGe 1 (1)]

def plane484GenLeaf0458Mult : Fin 42 → Nat := ![1242, 489, 451, 364, 487, 398, 12, 145, 44, 477, 715, 369, 179, 387, 106, 199, 152, 179, 122, 591, 9, 703, 335, 234, 169, 164, 670, 132, 1872, 158, 680, 498, 4269, 1333, 1872, 3079, 1563, 1080, 1740, 1872, 900, 3118]

theorem plane484GenLeaf0458 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0458Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0458Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0458Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0458Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 133
  · exact hroot.hOcc 135
  · exact hroot.hOcc 138
  · exact hroot.hOcc 191
  · exact hroot.hOcc 283
  · exact hroot.hOcc 412
  · exact hroot.hOcc 514
  · exact hroot.hOcc 545
  · exact hroot.hOcc 584
  · exact hroot.hOcc 674
  · exact hroot.hOcc 1101
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1276
  · exact hroot.hOcc 1285
  · exact hroot.hOcc 1310
  · exact hroot.hOcc 1402
  · exact hroot.hOcc 1409
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1536
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1641
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (27 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1

end QiushiMatmul
