import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0025Refs : Fin 50 → RowRef 726 49 := ![.occ 85, .occ 87, .occ 88, .occ 97, .occ 99, .occ 123, .occ 154, .occ 173, .occ 174, .occ 237, .occ 240, .occ 243, .occ 257, .occ 317, .occ 331, .occ 351, .occ 379, .occ 382, .occ 401, .occ 410, .occ 423, .occ 429, .occ 431, .occ 485, .occ 486, .occ 488, .occ 493, .occ 494, .occ 506, .occ 552, .occ 554, .occ 577, .occ 584, .occ 624, .occ 628, .occ 637, .occ 648, .occ 685, .occ 704, .occ 721, .sumGe, .nonneg 13, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchLe 29 (0), .branchLe 46 (0), .branchGe 32 (1), .branchGe 28 (1), .branchGe 22 (1)]

def plane491GenLeaf0025Mult : Fin 50 → Nat := ![2678, 75848, 4130, 21542, 15268, 79094, 38764, 46728, 45596, 1907, 12045, 57145, 4870, 17396, 10226, 75374, 1072, 7124, 86264, 19326, 332, 9764, 862, 2724, 2170, 3217, 4314, 25120, 9268, 2632, 424, 30620, 79322, 9176, 378, 46, 76648, 4222, 312, 18240, 109736, 137380, 32756, 53062, 21096, 22782, 1542, 470948, 264970, 384152]

theorem plane491GenLeaf0025 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hUB_46 : x 46 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0025Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0025Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0025Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0025Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 85
  · exact hroot.hOcc 87
  · exact hroot.hOcc 88
  · exact hroot.hOcc 97
  · exact hroot.hOcc 99
  · exact hroot.hOcc 123
  · exact hroot.hOcc 154
  · exact hroot.hOcc 173
  · exact hroot.hOcc 174
  · exact hroot.hOcc 237
  · exact hroot.hOcc 240
  · exact hroot.hOcc 243
  · exact hroot.hOcc 257
  · exact hroot.hOcc 317
  · exact hroot.hOcc 331
  · exact hroot.hOcc 351
  · exact hroot.hOcc 379
  · exact hroot.hOcc 382
  · exact hroot.hOcc 401
  · exact hroot.hOcc 410
  · exact hroot.hOcc 423
  · exact hroot.hOcc 429
  · exact hroot.hOcc 431
  · exact hroot.hOcc 485
  · exact hroot.hOcc 486
  · exact hroot.hOcc 488
  · exact hroot.hOcc 493
  · exact hroot.hOcc 494
  · exact hroot.hOcc 506
  · exact hroot.hOcc 552
  · exact hroot.hOcc 554
  · exact hroot.hOcc 577
  · exact hroot.hOcc 584
  · exact hroot.hOcc 624
  · exact hroot.hOcc 628
  · exact hroot.hOcc 637
  · exact hroot.hOcc 648
  · exact hroot.hOcc 685
  · exact hroot.hOcc 704
  · exact hroot.hOcc 721
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (13 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (46 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_46
  · change (∑ k, (if k = (32 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32
  · change (∑ k, (if k = (28 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (22 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22

end QiushiMatmul
