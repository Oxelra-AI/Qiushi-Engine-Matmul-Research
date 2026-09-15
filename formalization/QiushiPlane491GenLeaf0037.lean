import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0037Refs : Fin 50 → RowRef 726 49 := ![.occ 82, .occ 86, .occ 87, .occ 94, .occ 97, .occ 116, .occ 122, .occ 128, .occ 158, .occ 159, .occ 160, .occ 221, .occ 226, .occ 237, .occ 244, .occ 257, .occ 258, .occ 269, .occ 292, .occ 306, .occ 351, .occ 364, .occ 402, .occ 413, .occ 414, .occ 420, .occ 425, .occ 431, .occ 455, .occ 459, .occ 487, .occ 494, .occ 511, .occ 520, .occ 563, .occ 590, .occ 621, .occ 628, .occ 707, .occ 715, .occ 718, .sumGe, .nonneg 40, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchGe 29 (1), .branchLe 43 (0), .branchLe 9 (0), .branchGe 5 (1)]

def plane491GenLeaf0037Mult : Fin 50 → Nat := ![9886, 2052, 15030, 6972, 2938, 26006, 98, 6028, 6360, 5034, 8760, 11434, 3074, 3678, 14471, 18732, 7207, 10200, 1958, 5401, 1380, 16244, 12380, 2651, 2582, 9932, 7258, 13650, 7911, 2841, 2314, 2314, 4732, 404, 6312, 1096, 356, 2314, 134, 134, 17380, 38520, 740, 38520, 28588, 32558, 68472, 38386, 24638, 144284]

theorem plane491GenLeaf0037 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_43 : x 43 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0037Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0037Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0037Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0037Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 82
  · exact hroot.hOcc 86
  · exact hroot.hOcc 87
  · exact hroot.hOcc 94
  · exact hroot.hOcc 97
  · exact hroot.hOcc 116
  · exact hroot.hOcc 122
  · exact hroot.hOcc 128
  · exact hroot.hOcc 158
  · exact hroot.hOcc 159
  · exact hroot.hOcc 160
  · exact hroot.hOcc 221
  · exact hroot.hOcc 226
  · exact hroot.hOcc 237
  · exact hroot.hOcc 244
  · exact hroot.hOcc 257
  · exact hroot.hOcc 258
  · exact hroot.hOcc 269
  · exact hroot.hOcc 292
  · exact hroot.hOcc 306
  · exact hroot.hOcc 351
  · exact hroot.hOcc 364
  · exact hroot.hOcc 402
  · exact hroot.hOcc 413
  · exact hroot.hOcc 414
  · exact hroot.hOcc 420
  · exact hroot.hOcc 425
  · exact hroot.hOcc 431
  · exact hroot.hOcc 455
  · exact hroot.hOcc 459
  · exact hroot.hOcc 487
  · exact hroot.hOcc 494
  · exact hroot.hOcc 511
  · exact hroot.hOcc 520
  · exact hroot.hOcc 563
  · exact hroot.hOcc 590
  · exact hroot.hOcc 621
  · exact hroot.hOcc 628
  · exact hroot.hOcc 707
  · exact hroot.hOcc 715
  · exact hroot.hOcc 718
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (40 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (43 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (9 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (5 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5

end QiushiMatmul
