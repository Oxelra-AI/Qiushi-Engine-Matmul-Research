import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0049Refs : Fin 50 → RowRef 726 49 := ![.occ 93, .occ 97, .occ 100, .occ 101, .occ 106, .occ 109, .occ 122, .occ 151, .occ 152, .occ 161, .occ 198, .occ 199, .occ 219, .occ 230, .occ 231, .occ 299, .occ 304, .occ 305, .occ 318, .occ 324, .occ 329, .occ 332, .occ 363, .occ 430, .occ 431, .occ 470, .occ 494, .occ 511, .occ 539, .occ 543, .occ 560, .occ 583, .occ 584, .occ 586, .occ 603, .occ 623, .occ 626, .occ 661, .occ 665, .occ 712, .sumGe, .branchLe 31 (0), .branchLe 16 (0), .branchGe 27 (1), .branchLe 11 (0), .branchLe 23 (0), .branchLe 0 (0), .branchLe 43 (0), .branchLe 6 (0), .branchGe 44 (1)]

def plane491GenLeaf0049Mult : Fin 50 → Nat := ![29805, 12461, 1733, 58135, 26817, 12556, 7756, 29392, 16325, 10913, 13649, 47, 10147, 12153, 5858, 32936, 15008, 24396, 8, 1818, 16005, 3514, 29123, 10050, 11796, 6821, 14961, 22224, 5412, 8212, 8765, 6225, 2371, 27340, 526, 4549, 19292, 30360, 5858, 2365, 81917, 60054, 76030, 165823, 73327, 71340, 71244, 78403, 79552, 202520]

theorem plane491GenLeaf0049 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_44 : (1 : Int) ≤ x 44)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_43 : x 43 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0049Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0049Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0049Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0049Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 93
  · exact hroot.hOcc 97
  · exact hroot.hOcc 100
  · exact hroot.hOcc 101
  · exact hroot.hOcc 106
  · exact hroot.hOcc 109
  · exact hroot.hOcc 122
  · exact hroot.hOcc 151
  · exact hroot.hOcc 152
  · exact hroot.hOcc 161
  · exact hroot.hOcc 198
  · exact hroot.hOcc 199
  · exact hroot.hOcc 219
  · exact hroot.hOcc 230
  · exact hroot.hOcc 231
  · exact hroot.hOcc 299
  · exact hroot.hOcc 304
  · exact hroot.hOcc 305
  · exact hroot.hOcc 318
  · exact hroot.hOcc 324
  · exact hroot.hOcc 329
  · exact hroot.hOcc 332
  · exact hroot.hOcc 363
  · exact hroot.hOcc 430
  · exact hroot.hOcc 431
  · exact hroot.hOcc 470
  · exact hroot.hOcc 494
  · exact hroot.hOcc 511
  · exact hroot.hOcc 539
  · exact hroot.hOcc 543
  · exact hroot.hOcc 560
  · exact hroot.hOcc 583
  · exact hroot.hOcc 584
  · exact hroot.hOcc 586
  · exact hroot.hOcc 603
  · exact hroot.hOcc 623
  · exact hroot.hOcc 626
  · exact hroot.hOcc 661
  · exact hroot.hOcc 665
  · exact hroot.hOcc 712
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (11 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (23 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (0 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (43 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (6 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (44 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_44

end QiushiMatmul
