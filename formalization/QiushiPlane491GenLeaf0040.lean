import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0040Refs : Fin 50 → RowRef 726 49 := ![.occ 78, .occ 97, .occ 107, .occ 112, .occ 116, .occ 131, .occ 157, .occ 184, .occ 197, .occ 230, .occ 240, .occ 287, .occ 304, .occ 318, .occ 327, .occ 364, .occ 379, .occ 394, .occ 401, .occ 402, .occ 405, .occ 415, .occ 430, .occ 431, .occ 470, .occ 552, .occ 568, .occ 574, .occ 584, .occ 622, .occ 628, .occ 632, .occ 634, .occ 657, .occ 659, .occ 685, .occ 707, .occ 714, .occ 718, .sumGe, .nonneg 8, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchGe 29 (1), .branchLe 43 (0), .branchGe 9 (1), .branchLe 0 (0), .branchLe 23 (0), .branchGe 35 (1)]

def plane491GenLeaf0040Mult : Fin 50 → Nat := ![9465, 6531, 11982, 2334, 2621, 7462, 22329, 16615, 3869, 9826, 7580, 5099, 10418, 2998, 2765, 2527, 2238, 23892, 3787, 27219, 21251, 16240, 6302, 7114, 7113, 8132, 306, 5439, 8151, 3898, 8903, 4063, 12635, 2254, 343, 5458, 7469, 6316, 5603, 47289, 173, 22132, 20399, 26044, 132392, 34948, 48432, 33554, 31548, 134495]

theorem plane491GenLeaf0040 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_43 : x 43 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0040Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0040Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0040Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0040Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 78
  · exact hroot.hOcc 97
  · exact hroot.hOcc 107
  · exact hroot.hOcc 112
  · exact hroot.hOcc 116
  · exact hroot.hOcc 131
  · exact hroot.hOcc 157
  · exact hroot.hOcc 184
  · exact hroot.hOcc 197
  · exact hroot.hOcc 230
  · exact hroot.hOcc 240
  · exact hroot.hOcc 287
  · exact hroot.hOcc 304
  · exact hroot.hOcc 318
  · exact hroot.hOcc 327
  · exact hroot.hOcc 364
  · exact hroot.hOcc 379
  · exact hroot.hOcc 394
  · exact hroot.hOcc 401
  · exact hroot.hOcc 402
  · exact hroot.hOcc 405
  · exact hroot.hOcc 415
  · exact hroot.hOcc 430
  · exact hroot.hOcc 431
  · exact hroot.hOcc 470
  · exact hroot.hOcc 552
  · exact hroot.hOcc 568
  · exact hroot.hOcc 574
  · exact hroot.hOcc 584
  · exact hroot.hOcc 622
  · exact hroot.hOcc 628
  · exact hroot.hOcc 632
  · exact hroot.hOcc 634
  · exact hroot.hOcc 657
  · exact hroot.hOcc 659
  · exact hroot.hOcc 685
  · exact hroot.hOcc 707
  · exact hroot.hOcc 714
  · exact hroot.hOcc 718
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (43 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (9 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9
  · change (∑ k, (if k = (0 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (23 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (35 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35

end QiushiMatmul
