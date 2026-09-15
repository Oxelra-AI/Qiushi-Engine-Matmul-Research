import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0102Refs : Fin 49 → RowRef 726 49 := ![.occ 94, .occ 96, .occ 98, .occ 100, .occ 109, .occ 112, .occ 116, .occ 122, .occ 154, .occ 159, .occ 160, .occ 161, .occ 197, .occ 257, .occ 276, .occ 323, .occ 328, .occ 331, .occ 350, .occ 364, .occ 393, .occ 396, .occ 402, .occ 422, .occ 430, .occ 482, .occ 484, .occ 495, .occ 531, .occ 562, .occ 565, .occ 576, .occ 584, .occ 625, .occ 632, .occ 640, .occ 671, .occ 722, .sumGe, .nonneg 37, .branchGe 31 (1), .branchGe 44 (1), .branchLe 6 (0), .branchLe 39 (0), .branchGe 28 (1), .branchLe 36 (0), .branchGe 15 (1), .branchLe 9 (0), .branchGe 29 (1)]

def plane491GenLeaf0102Mult : Fin 49 → Nat := ![2175, 1329, 6208, 5175, 7766, 2232, 7654, 1569, 4108, 5192, 3767, 1787, 5898, 2419, 794, 3055, 1553, 3346, 3239, 178, 3239, 2035, 2329, 5014, 4392, 5326, 5950, 4089, 3310, 1225, 3946, 2240, 4504, 6484, 89, 2507, 236, 1170, 16550, 2952, 34228, 22962, 13954, 12461, 22896, 16461, 11758, 6744, 39645]

theorem plane491GenLeaf0102 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_44 : (1 : Int) ≤ x 44)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0102Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0102Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0102Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0102Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 94
  · exact hroot.hOcc 96
  · exact hroot.hOcc 98
  · exact hroot.hOcc 100
  · exact hroot.hOcc 109
  · exact hroot.hOcc 112
  · exact hroot.hOcc 116
  · exact hroot.hOcc 122
  · exact hroot.hOcc 154
  · exact hroot.hOcc 159
  · exact hroot.hOcc 160
  · exact hroot.hOcc 161
  · exact hroot.hOcc 197
  · exact hroot.hOcc 257
  · exact hroot.hOcc 276
  · exact hroot.hOcc 323
  · exact hroot.hOcc 328
  · exact hroot.hOcc 331
  · exact hroot.hOcc 350
  · exact hroot.hOcc 364
  · exact hroot.hOcc 393
  · exact hroot.hOcc 396
  · exact hroot.hOcc 402
  · exact hroot.hOcc 422
  · exact hroot.hOcc 430
  · exact hroot.hOcc 482
  · exact hroot.hOcc 484
  · exact hroot.hOcc 495
  · exact hroot.hOcc 531
  · exact hroot.hOcc 562
  · exact hroot.hOcc 565
  · exact hroot.hOcc 576
  · exact hroot.hOcc 584
  · exact hroot.hOcc 625
  · exact hroot.hOcc 632
  · exact hroot.hOcc 640
  · exact hroot.hOcc 671
  · exact hroot.hOcc 722
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (37 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_44
  · change (∑ k, (if k = (6 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (39 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (28 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (36 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (15 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (9 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (29 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29

end QiushiMatmul
