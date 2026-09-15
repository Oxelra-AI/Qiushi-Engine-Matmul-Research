import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0041Refs : Fin 50 → RowRef 726 49 := ![.occ 80, .occ 88, .occ 97, .occ 105, .occ 109, .occ 116, .occ 143, .occ 146, .occ 173, .occ 197, .occ 212, .occ 241, .occ 257, .occ 287, .occ 304, .occ 324, .occ 366, .occ 372, .occ 394, .occ 402, .occ 420, .occ 427, .occ 430, .occ 513, .occ 530, .occ 565, .occ 574, .occ 575, .occ 584, .occ 594, .occ 621, .occ 628, .occ 629, .occ 630, .occ 683, .occ 686, .occ 702, .occ 722, .sumGe, .nonneg 10, .nonneg 14, .nonneg 48, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchGe 29 (1), .branchLe 43 (0), .branchGe 9 (1), .branchLe 0 (0), .branchGe 23 (1)]

def plane491GenLeaf0041Mult : Fin 50 → Nat := ![1121, 585, 205, 201, 100, 740, 37, 205, 641, 491, 581, 1684, 150, 276, 87, 69, 137, 130, 153, 102, 170, 112, 111, 20, 758, 168, 874, 197, 42, 328, 346, 89, 22, 736, 494, 284, 79, 496, 1795, 546, 2118, 551, 637, 1393, 1162, 5409, 774, 6023, 462, 4667]

theorem plane491GenLeaf0041 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_43 : x 43 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0041Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0041Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0041Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0041Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 80
  · exact hroot.hOcc 88
  · exact hroot.hOcc 97
  · exact hroot.hOcc 105
  · exact hroot.hOcc 109
  · exact hroot.hOcc 116
  · exact hroot.hOcc 143
  · exact hroot.hOcc 146
  · exact hroot.hOcc 173
  · exact hroot.hOcc 197
  · exact hroot.hOcc 212
  · exact hroot.hOcc 241
  · exact hroot.hOcc 257
  · exact hroot.hOcc 287
  · exact hroot.hOcc 304
  · exact hroot.hOcc 324
  · exact hroot.hOcc 366
  · exact hroot.hOcc 372
  · exact hroot.hOcc 394
  · exact hroot.hOcc 402
  · exact hroot.hOcc 420
  · exact hroot.hOcc 427
  · exact hroot.hOcc 430
  · exact hroot.hOcc 513
  · exact hroot.hOcc 530
  · exact hroot.hOcc 565
  · exact hroot.hOcc 574
  · exact hroot.hOcc 575
  · exact hroot.hOcc 584
  · exact hroot.hOcc 594
  · exact hroot.hOcc 621
  · exact hroot.hOcc 628
  · exact hroot.hOcc 629
  · exact hroot.hOcc 630
  · exact hroot.hOcc 683
  · exact hroot.hOcc 686
  · exact hroot.hOcc 702
  · exact hroot.hOcc 722
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (14 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (48 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (43 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (9 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9
  · change (∑ k, (if k = (0 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (23 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23

end QiushiMatmul
