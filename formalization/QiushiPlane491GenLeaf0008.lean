import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0008Refs : Fin 50 → RowRef 726 49 := ![.occ 105, .occ 115, .occ 120, .occ 122, .occ 126, .occ 231, .occ 237, .occ 248, .occ 255, .occ 258, .occ 271, .occ 287, .occ 289, .occ 293, .occ 326, .occ 332, .occ 403, .occ 410, .occ 414, .occ 423, .occ 442, .occ 493, .occ 497, .occ 513, .occ 516, .occ 540, .occ 549, .occ 563, .occ 574, .occ 590, .occ 594, .occ 623, .occ 647, .occ 656, .occ 671, .occ 676, .occ 706, .sumGe, .nonneg 48, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchLe 29 (0), .branchLe 46 (0), .branchLe 32 (0), .branchLe 38 (0), .branchGe 6 (1), .branchLe 0 (0), .branchLe 43 (0), .branchGe 41 (1)]

def plane491GenLeaf0008Mult : Fin 50 → Nat := ![3550, 1897, 43731, 10609, 25573, 3292, 2811, 10779, 1710, 14889, 75827, 4905, 25560, 20624, 4687, 10315, 3175, 19576, 9659, 28629, 8482, 11744, 7731, 30466, 28639, 13994, 1395, 4160, 50260, 3338, 4857, 9917, 34465, 2072, 11860, 602, 41894, 111512, 16840, 57029, 89023, 108174, 56395, 19358, 82883, 111512, 217486, 108701, 54562, 314875]

theorem plane491GenLeaf0008 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_41 : (1 : Int) ≤ x 41)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_46 : x 46 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_43 : x 43 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0008Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0008Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0008Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0008Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 105
  · exact hroot.hOcc 115
  · exact hroot.hOcc 120
  · exact hroot.hOcc 122
  · exact hroot.hOcc 126
  · exact hroot.hOcc 231
  · exact hroot.hOcc 237
  · exact hroot.hOcc 248
  · exact hroot.hOcc 255
  · exact hroot.hOcc 258
  · exact hroot.hOcc 271
  · exact hroot.hOcc 287
  · exact hroot.hOcc 289
  · exact hroot.hOcc 293
  · exact hroot.hOcc 326
  · exact hroot.hOcc 332
  · exact hroot.hOcc 403
  · exact hroot.hOcc 410
  · exact hroot.hOcc 414
  · exact hroot.hOcc 423
  · exact hroot.hOcc 442
  · exact hroot.hOcc 493
  · exact hroot.hOcc 497
  · exact hroot.hOcc 513
  · exact hroot.hOcc 516
  · exact hroot.hOcc 540
  · exact hroot.hOcc 549
  · exact hroot.hOcc 563
  · exact hroot.hOcc 574
  · exact hroot.hOcc 590
  · exact hroot.hOcc 594
  · exact hroot.hOcc 623
  · exact hroot.hOcc 647
  · exact hroot.hOcc 656
  · exact hroot.hOcc 671
  · exact hroot.hOcc 676
  · exact hroot.hOcc 706
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (48 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (46 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_46
  · change (∑ k, (if k = (32 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (38 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (6 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (0 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (43 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (41 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_41

end QiushiMatmul
