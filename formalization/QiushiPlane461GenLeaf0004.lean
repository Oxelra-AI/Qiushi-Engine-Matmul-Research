import QiushiPlane461GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane461GenLeaf0004Refs : Fin 63 → RowRef 151 62 := ![.occ 1, .occ 8, .occ 15, .occ 20, .occ 24, .occ 30, .occ 31, .occ 33, .occ 34, .occ 36, .occ 37, .occ 41, .occ 43, .occ 46, .occ 54, .occ 58, .occ 64, .occ 69, .occ 77, .occ 81, .occ 84, .occ 85, .occ 86, .occ 87, .occ 88, .occ 89, .occ 92, .occ 93, .occ 96, .occ 98, .occ 104, .occ 106, .occ 108, .occ 120, .occ 121, .occ 125, .occ 127, .occ 128, .occ 133, .occ 136, .occ 148, .occ 149, .sumGe, .nonneg 6, .nonneg 9, .nonneg 10, .nonneg 13, .nonneg 23, .nonneg 25, .nonneg 32, .nonneg 33, .nonneg 36, .nonneg 38, .nonneg 39, .nonneg 40, .nonneg 44, .nonneg 53, .nonneg 54, .nonneg 55, .nonneg 57, .branchGe 16 (1), .branchLe 48 (0), .branchGe 21 (1)]

def plane461GenLeaf0004Mult : Fin 63 → Nat := ![170439, 324941, 150312, 339567, 31120, 278828, 110068, 118599, 115032, 70176, 39022, 92501, 249122, 4238, 190933, 135635, 87287, 11498, 206343, 66403, 100830, 19678, 26036, 138718, 47194, 82510, 89406, 89559, 167532, 44024, 145198, 14326, 102929, 61364, 19017, 11823, 15262, 17847, 33215, 38567, 31609, 55850, 476919, 226325, 580477, 186597, 37954, 31539, 69504, 28067, 236483, 23786, 283812, 348645, 70181, 275225, 296506, 56208, 88722, 187803, 233510, 297564, 1975482]

theorem plane461GenLeaf0004 (x : Fin 62 → Int)
    (hroot : plane461GenOccSys.RootHolds x)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hUB_48 : x 48 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane461GenLeaf0004Refs i).resolveCoeff plane461GenOccSys j)
    (fun i => (plane461GenLeaf0004Refs i).resolveRhs plane461GenOccSys) plane461GenLeaf0004Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane461GenLeaf0004Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · exact hroot.hOcc 8
  · exact hroot.hOcc 15
  · exact hroot.hOcc 20
  · exact hroot.hOcc 24
  · exact hroot.hOcc 30
  · exact hroot.hOcc 31
  · exact hroot.hOcc 33
  · exact hroot.hOcc 34
  · exact hroot.hOcc 36
  · exact hroot.hOcc 37
  · exact hroot.hOcc 41
  · exact hroot.hOcc 43
  · exact hroot.hOcc 46
  · exact hroot.hOcc 54
  · exact hroot.hOcc 58
  · exact hroot.hOcc 64
  · exact hroot.hOcc 69
  · exact hroot.hOcc 77
  · exact hroot.hOcc 81
  · exact hroot.hOcc 84
  · exact hroot.hOcc 85
  · exact hroot.hOcc 86
  · exact hroot.hOcc 87
  · exact hroot.hOcc 88
  · exact hroot.hOcc 89
  · exact hroot.hOcc 92
  · exact hroot.hOcc 93
  · exact hroot.hOcc 96
  · exact hroot.hOcc 98
  · exact hroot.hOcc 104
  · exact hroot.hOcc 106
  · exact hroot.hOcc 108
  · exact hroot.hOcc 120
  · exact hroot.hOcc 121
  · exact hroot.hOcc 125
  · exact hroot.hOcc 127
  · exact hroot.hOcc 128
  · exact hroot.hOcc 133
  · exact hroot.hOcc 136
  · exact hroot.hOcc 148
  · exact hroot.hOcc 149
  · change (∑ j, (-1 : Int) * x j) ≤ -plane461GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (9 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 9
  · change (∑ k, (if k = (10 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (13 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (23 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (25 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (32 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (33 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (36 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (38 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (39 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (40 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (44 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (53 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (54 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 54
  · change (∑ k, (if k = (55 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (57 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 57
  · change (∑ k, (if k = (16 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (48 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_48
  · change (∑ k, (if k = (21 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21

end QiushiMatmul
