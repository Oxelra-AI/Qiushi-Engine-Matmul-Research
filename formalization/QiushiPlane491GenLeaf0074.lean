import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0074Refs : Fin 50 → RowRef 726 49 := ![.occ 83, .occ 113, .occ 118, .occ 121, .occ 167, .occ 172, .occ 178, .occ 201, .occ 219, .occ 222, .occ 230, .occ 231, .occ 243, .occ 267, .occ 312, .occ 329, .occ 334, .occ 350, .occ 355, .occ 359, .occ 364, .occ 377, .occ 382, .occ 393, .occ 394, .occ 413, .occ 415, .occ 423, .occ 495, .occ 510, .occ 599, .occ 603, .occ 606, .occ 611, .occ 640, .occ 669, .occ 691, .occ 699, .occ 711, .sumGe, .nonneg 7, .nonneg 24, .branchGe 31 (1), .branchLe 44 (0), .branchLe 11 (0), .branchLe 27 (0), .branchLe 22 (0), .branchLe 15 (0), .branchLe 12 (0), .branchGe 14 (1)]

def plane491GenLeaf0074Mult : Fin 50 → Nat := ![11394, 2743, 6727, 3074, 5209, 1837, 1848, 578, 1583, 3131, 2056, 540, 94, 1308, 522, 2689, 4323, 1299, 2793, 537, 2449, 4047, 197, 1478, 5208, 3735, 318, 1270, 1493, 243, 2359, 1556, 4476, 767, 2808, 4511, 1445, 1083, 1305, 13611, 4734, 2220, 30575, 7865, 13611, 11545, 13611, 9255, 11539, 30535]

theorem plane491GenLeaf0074 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0074Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0074Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0074Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0074Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 83
  · exact hroot.hOcc 113
  · exact hroot.hOcc 118
  · exact hroot.hOcc 121
  · exact hroot.hOcc 167
  · exact hroot.hOcc 172
  · exact hroot.hOcc 178
  · exact hroot.hOcc 201
  · exact hroot.hOcc 219
  · exact hroot.hOcc 222
  · exact hroot.hOcc 230
  · exact hroot.hOcc 231
  · exact hroot.hOcc 243
  · exact hroot.hOcc 267
  · exact hroot.hOcc 312
  · exact hroot.hOcc 329
  · exact hroot.hOcc 334
  · exact hroot.hOcc 350
  · exact hroot.hOcc 355
  · exact hroot.hOcc 359
  · exact hroot.hOcc 364
  · exact hroot.hOcc 377
  · exact hroot.hOcc 382
  · exact hroot.hOcc 393
  · exact hroot.hOcc 394
  · exact hroot.hOcc 413
  · exact hroot.hOcc 415
  · exact hroot.hOcc 423
  · exact hroot.hOcc 495
  · exact hroot.hOcc 510
  · exact hroot.hOcc 599
  · exact hroot.hOcc 603
  · exact hroot.hOcc 606
  · exact hroot.hOcc 611
  · exact hroot.hOcc 640
  · exact hroot.hOcc 669
  · exact hroot.hOcc 691
  · exact hroot.hOcc 699
  · exact hroot.hOcc 711
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (24 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (11 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (22 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (15 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (12 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (14 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14

end QiushiMatmul
