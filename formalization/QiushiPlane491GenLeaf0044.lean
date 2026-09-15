import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0044Refs : Fin 49 → RowRef 726 49 := ![.occ 80, .occ 87, .occ 108, .occ 109, .occ 113, .occ 114, .occ 115, .occ 116, .occ 120, .occ 204, .occ 240, .occ 241, .occ 254, .occ 256, .occ 258, .occ 267, .occ 292, .occ 325, .occ 336, .occ 345, .occ 358, .occ 373, .occ 382, .occ 398, .occ 401, .occ 431, .occ 446, .occ 493, .occ 569, .occ 628, .occ 643, .occ 653, .occ 654, .occ 668, .occ 673, .occ 686, .occ 691, .occ 704, .occ 722, .sumGe, .nonneg 23, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchGe 29 (1), .branchGe 43 (1), .branchLe 32 (0), .branchLe 0 (0), .branchGe 21 (1)]

def plane491GenLeaf0044Mult : Fin 49 → Nat := ![410, 72, 1413, 1238, 1588, 503, 1550, 1024, 419, 207, 168, 994, 163, 465, 646, 448, 803, 191, 2058, 2540, 54, 535, 809, 1465, 191, 111, 1153, 461, 1605, 121, 794, 163, 596, 20, 646, 767, 626, 453, 315, 3471, 479, 3156, 767, 2993, 6985, 11703, 2024, 2530, 11951]

theorem plane491GenLeaf0044 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_43 : (1 : Int) ≤ x 43)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0044Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0044Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0044Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0044Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 80
  · exact hroot.hOcc 87
  · exact hroot.hOcc 108
  · exact hroot.hOcc 109
  · exact hroot.hOcc 113
  · exact hroot.hOcc 114
  · exact hroot.hOcc 115
  · exact hroot.hOcc 116
  · exact hroot.hOcc 120
  · exact hroot.hOcc 204
  · exact hroot.hOcc 240
  · exact hroot.hOcc 241
  · exact hroot.hOcc 254
  · exact hroot.hOcc 256
  · exact hroot.hOcc 258
  · exact hroot.hOcc 267
  · exact hroot.hOcc 292
  · exact hroot.hOcc 325
  · exact hroot.hOcc 336
  · exact hroot.hOcc 345
  · exact hroot.hOcc 358
  · exact hroot.hOcc 373
  · exact hroot.hOcc 382
  · exact hroot.hOcc 398
  · exact hroot.hOcc 401
  · exact hroot.hOcc 431
  · exact hroot.hOcc 446
  · exact hroot.hOcc 493
  · exact hroot.hOcc 569
  · exact hroot.hOcc 628
  · exact hroot.hOcc 643
  · exact hroot.hOcc 653
  · exact hroot.hOcc 654
  · exact hroot.hOcc 668
  · exact hroot.hOcc 673
  · exact hroot.hOcc 686
  · exact hroot.hOcc 691
  · exact hroot.hOcc 704
  · exact hroot.hOcc 722
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (23 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (43 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_43
  · change (∑ k, (if k = (32 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (0 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (21 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21

end QiushiMatmul
