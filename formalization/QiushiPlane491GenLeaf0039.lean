import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0039Refs : Fin 50 → RowRef 726 49 := ![.occ 78, .occ 80, .occ 89, .occ 97, .occ 104, .occ 113, .occ 116, .occ 120, .occ 131, .occ 158, .occ 182, .occ 241, .occ 257, .occ 258, .occ 260, .occ 292, .occ 299, .occ 324, .occ 326, .occ 327, .occ 372, .occ 373, .occ 420, .occ 422, .occ 427, .occ 431, .occ 466, .occ 471, .occ 486, .occ 494, .occ 515, .occ 573, .occ 574, .occ 584, .occ 621, .occ 624, .occ 628, .occ 685, .occ 686, .sumGe, .nonneg 23, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchGe 29 (1), .branchLe 43 (0), .branchGe 9 (1), .branchLe 0 (0), .branchLe 35 (0), .branchGe 4 (1)]

def plane491GenLeaf0039Mult : Fin 50 → Nat := ![37125, 240691, 157418, 102439, 185574, 93219, 114793, 40103, 269137, 64125, 27070, 130631, 58664, 33093, 5509, 87077, 51731, 34739, 20457, 12749, 92712, 47750, 66174, 11168, 6521, 36566, 18366, 23921, 35027, 57808, 79762, 30923, 97561, 60834, 51633, 31207, 36380, 74698, 104030, 341892, 25010, 329143, 244511, 290161, 386653, 341892, 785203, 336383, 305512, 842181]

theorem plane491GenLeaf0039 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    (hUB_43 : x 43 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0039Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0039Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0039Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0039Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 78
  · exact hroot.hOcc 80
  · exact hroot.hOcc 89
  · exact hroot.hOcc 97
  · exact hroot.hOcc 104
  · exact hroot.hOcc 113
  · exact hroot.hOcc 116
  · exact hroot.hOcc 120
  · exact hroot.hOcc 131
  · exact hroot.hOcc 158
  · exact hroot.hOcc 182
  · exact hroot.hOcc 241
  · exact hroot.hOcc 257
  · exact hroot.hOcc 258
  · exact hroot.hOcc 260
  · exact hroot.hOcc 292
  · exact hroot.hOcc 299
  · exact hroot.hOcc 324
  · exact hroot.hOcc 326
  · exact hroot.hOcc 327
  · exact hroot.hOcc 372
  · exact hroot.hOcc 373
  · exact hroot.hOcc 420
  · exact hroot.hOcc 422
  · exact hroot.hOcc 427
  · exact hroot.hOcc 431
  · exact hroot.hOcc 466
  · exact hroot.hOcc 471
  · exact hroot.hOcc 486
  · exact hroot.hOcc 494
  · exact hroot.hOcc 515
  · exact hroot.hOcc 573
  · exact hroot.hOcc 574
  · exact hroot.hOcc 584
  · exact hroot.hOcc 621
  · exact hroot.hOcc 624
  · exact hroot.hOcc 628
  · exact hroot.hOcc 685
  · exact hroot.hOcc 686
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (23 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (43 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (9 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9
  · change (∑ k, (if k = (0 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (35 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (4 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4

end QiushiMatmul
