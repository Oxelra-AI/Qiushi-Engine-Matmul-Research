import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0085Refs : Fin 50 → RowRef 726 49 := ![.occ 85, .occ 87, .occ 94, .occ 97, .occ 100, .occ 106, .occ 116, .occ 139, .occ 146, .occ 171, .occ 231, .occ 297, .occ 315, .occ 323, .occ 338, .occ 350, .occ 355, .occ 359, .occ 368, .occ 382, .occ 392, .occ 393, .occ 431, .occ 481, .occ 482, .occ 484, .occ 485, .occ 504, .occ 517, .occ 529, .occ 556, .occ 567, .occ 601, .occ 606, .occ 632, .occ 640, .occ 642, .occ 662, .occ 665, .occ 715, .sumGe, .nonneg 13, .nonneg 33, .nonneg 38, .branchGe 31 (1), .branchLe 44 (0), .branchLe 11 (0), .branchGe 27 (1), .branchLe 43 (0), .branchGe 17 (1)]

def plane491GenLeaf0085Mult : Fin 50 → Nat := ![4441, 9066, 66260, 17883, 33126, 39385, 3096, 5483, 6795, 2763, 12307, 5444, 6933, 66260, 17016, 12566, 8817, 2151, 4984, 12498, 4960, 22224, 14408, 2320, 10378, 9033, 10588, 14252, 4365, 11854, 2313, 19491, 2068, 5774, 19535, 5979, 9322, 3779, 11935, 5253, 66260, 44004, 11473, 18187, 123643, 60281, 37693, 204403, 48509, 201439]

theorem plane491GenLeaf0085 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_43 : x 43 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0085Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0085Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0085Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0085Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 85
  · exact hroot.hOcc 87
  · exact hroot.hOcc 94
  · exact hroot.hOcc 97
  · exact hroot.hOcc 100
  · exact hroot.hOcc 106
  · exact hroot.hOcc 116
  · exact hroot.hOcc 139
  · exact hroot.hOcc 146
  · exact hroot.hOcc 171
  · exact hroot.hOcc 231
  · exact hroot.hOcc 297
  · exact hroot.hOcc 315
  · exact hroot.hOcc 323
  · exact hroot.hOcc 338
  · exact hroot.hOcc 350
  · exact hroot.hOcc 355
  · exact hroot.hOcc 359
  · exact hroot.hOcc 368
  · exact hroot.hOcc 382
  · exact hroot.hOcc 392
  · exact hroot.hOcc 393
  · exact hroot.hOcc 431
  · exact hroot.hOcc 481
  · exact hroot.hOcc 482
  · exact hroot.hOcc 484
  · exact hroot.hOcc 485
  · exact hroot.hOcc 504
  · exact hroot.hOcc 517
  · exact hroot.hOcc 529
  · exact hroot.hOcc 556
  · exact hroot.hOcc 567
  · exact hroot.hOcc 601
  · exact hroot.hOcc 606
  · exact hroot.hOcc 632
  · exact hroot.hOcc 640
  · exact hroot.hOcc 642
  · exact hroot.hOcc 662
  · exact hroot.hOcc 665
  · exact hroot.hOcc 715
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (13 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (33 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (38 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (11 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (27 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (43 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (17 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17

end QiushiMatmul
