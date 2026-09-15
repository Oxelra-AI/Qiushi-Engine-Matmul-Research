import QiushiPlane458GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane458GenLeaf0004Refs : Fin 57 → RowRef 203 56 := ![.occ 19, .occ 24, .occ 28, .occ 30, .occ 32, .occ 35, .occ 40, .occ 49, .occ 51, .occ 55, .occ 61, .occ 66, .occ 74, .occ 75, .occ 80, .occ 81, .occ 84, .occ 85, .occ 86, .occ 95, .occ 98, .occ 99, .occ 104, .occ 106, .occ 111, .occ 113, .occ 114, .occ 117, .occ 119, .occ 129, .occ 135, .occ 144, .occ 157, .occ 164, .occ 165, .occ 173, .occ 176, .occ 177, .occ 182, .occ 188, .occ 194, .occ 195, .occ 199, .occ 201, .occ 202, .sumGe, .nonneg 19, .nonneg 29, .nonneg 34, .nonneg 43, .nonneg 48, .nonneg 53, .branchLe 46 (0), .branchGe 30 (1), .branchLe 10 (0), .branchLe 3 (0), .branchGe 40 (1)]

def plane458GenLeaf0004Mult : Fin 57 → Nat := ![71991, 2319996, 1682292, 1873382, 284002, 1210617, 1881680, 3051595, 1059588, 2916685, 653605, 3221894, 1106263, 947458, 3251411, 3490765, 1240385, 819681, 405722, 3827042, 1234498, 2471275, 1315262, 2645947, 923034, 764703, 1523748, 958166, 606749, 353346, 494655, 883341, 816490, 829938, 1136396, 312803, 870343, 1425365, 690321, 52209, 1305872, 452894, 5909, 1872090, 415734, 7125241, 457550, 2894045, 2136626, 1669457, 60140, 1930908, 7073032, 3784676, 5530042, 4707197, 21198333]

theorem plane458GenLeaf0004 (x : Fin 56 → Int)
    (hroot : plane458GenOccSys.RootHolds x)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_40 : (1 : Int) ≤ x 40)
    (hUB_46 : x 46 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane458GenLeaf0004Refs i).resolveCoeff plane458GenOccSys j)
    (fun i => (plane458GenLeaf0004Refs i).resolveRhs plane458GenOccSys) plane458GenLeaf0004Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane458GenLeaf0004Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 19
  · exact hroot.hOcc 24
  · exact hroot.hOcc 28
  · exact hroot.hOcc 30
  · exact hroot.hOcc 32
  · exact hroot.hOcc 35
  · exact hroot.hOcc 40
  · exact hroot.hOcc 49
  · exact hroot.hOcc 51
  · exact hroot.hOcc 55
  · exact hroot.hOcc 61
  · exact hroot.hOcc 66
  · exact hroot.hOcc 74
  · exact hroot.hOcc 75
  · exact hroot.hOcc 80
  · exact hroot.hOcc 81
  · exact hroot.hOcc 84
  · exact hroot.hOcc 85
  · exact hroot.hOcc 86
  · exact hroot.hOcc 95
  · exact hroot.hOcc 98
  · exact hroot.hOcc 99
  · exact hroot.hOcc 104
  · exact hroot.hOcc 106
  · exact hroot.hOcc 111
  · exact hroot.hOcc 113
  · exact hroot.hOcc 114
  · exact hroot.hOcc 117
  · exact hroot.hOcc 119
  · exact hroot.hOcc 129
  · exact hroot.hOcc 135
  · exact hroot.hOcc 144
  · exact hroot.hOcc 157
  · exact hroot.hOcc 164
  · exact hroot.hOcc 165
  · exact hroot.hOcc 173
  · exact hroot.hOcc 176
  · exact hroot.hOcc 177
  · exact hroot.hOcc 182
  · exact hroot.hOcc 188
  · exact hroot.hOcc 194
  · exact hroot.hOcc 195
  · exact hroot.hOcc 199
  · exact hroot.hOcc 201
  · exact hroot.hOcc 202
  · change (∑ j, (-1 : Int) * x j) ≤ -plane458GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (19 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (29 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (34 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 34
  · change (∑ k, (if k = (43 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 43
  · change (∑ k, (if k = (48 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (53 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (46 : Fin 56) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_46
  · change (∑ k, (if k = (30 : Fin 56) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (10 : Fin 56) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (3 : Fin 56) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (40 : Fin 56) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_40

end QiushiMatmul
