import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0017Refs : Fin 50 → RowRef 726 49 := ![.occ 82, .occ 102, .occ 107, .occ 114, .occ 119, .occ 121, .occ 133, .occ 176, .occ 179, .occ 187, .occ 221, .occ 232, .occ 246, .occ 272, .occ 287, .occ 304, .occ 318, .occ 332, .occ 367, .occ 370, .occ 382, .occ 389, .occ 399, .occ 419, .occ 421, .occ 422, .occ 431, .occ 494, .occ 532, .occ 565, .occ 616, .occ 617, .occ 629, .occ 651, .occ 664, .occ 685, .occ 697, .occ 720, .sumGe, .nonneg 13, .nonneg 46, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchLe 29 (0), .branchLe 32 (0), .branchGe 38 (1), .branchLe 1 (0), .branchLe 10 (0), .branchGe 7 (1)]

def plane491GenLeaf0017Mult : Fin 50 → Nat := ![11002, 9720, 3098, 10620, 6991, 4575, 6417, 4959, 143, 6774, 4956, 1966, 335, 4575, 261, 4911, 5004, 351, 3891, 1206, 2712, 1794, 5421, 1691, 5655, 2437, 2850, 1113, 1206, 1596, 1038, 846, 2346, 48, 1635, 5772, 519, 2907, 13683, 871, 6448, 6432, 1063, 7772, 3989, 11532, 41440, 5565, 13683, 72459]

theorem plane491GenLeaf0017 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_46 : x 46 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0017Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0017Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0017Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0017Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 82
  · exact hroot.hOcc 102
  · exact hroot.hOcc 107
  · exact hroot.hOcc 114
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 133
  · exact hroot.hOcc 176
  · exact hroot.hOcc 179
  · exact hroot.hOcc 187
  · exact hroot.hOcc 221
  · exact hroot.hOcc 232
  · exact hroot.hOcc 246
  · exact hroot.hOcc 272
  · exact hroot.hOcc 287
  · exact hroot.hOcc 304
  · exact hroot.hOcc 318
  · exact hroot.hOcc 332
  · exact hroot.hOcc 367
  · exact hroot.hOcc 370
  · exact hroot.hOcc 382
  · exact hroot.hOcc 389
  · exact hroot.hOcc 399
  · exact hroot.hOcc 419
  · exact hroot.hOcc 421
  · exact hroot.hOcc 422
  · exact hroot.hOcc 431
  · exact hroot.hOcc 494
  · exact hroot.hOcc 532
  · exact hroot.hOcc 565
  · exact hroot.hOcc 616
  · exact hroot.hOcc 617
  · exact hroot.hOcc 629
  · exact hroot.hOcc 651
  · exact hroot.hOcc 664
  · exact hroot.hOcc 685
  · exact hroot.hOcc 697
  · exact hroot.hOcc 720
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (13 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (46 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (32 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (38 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38
  · change (∑ k, (if k = (1 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (10 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (7 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7

end QiushiMatmul
