import QiushiPlane461GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane461GenLeaf0002Refs : Fin 62 → RowRef 151 62 := ![.occ 11, .occ 13, .occ 18, .occ 19, .occ 25, .occ 26, .occ 29, .occ 30, .occ 33, .occ 34, .occ 36, .occ 38, .occ 40, .occ 41, .occ 42, .occ 43, .occ 44, .occ 46, .occ 51, .occ 53, .occ 57, .occ 58, .occ 70, .occ 82, .occ 86, .occ 87, .occ 89, .occ 90, .occ 91, .occ 94, .occ 95, .occ 96, .occ 98, .occ 99, .occ 100, .occ 102, .occ 103, .occ 107, .occ 109, .occ 110, .occ 112, .occ 114, .occ 117, .occ 126, .occ 131, .occ 135, .occ 136, .occ 148, .occ 150, .sumGe, .nonneg 6, .nonneg 9, .nonneg 32, .nonneg 33, .nonneg 36, .nonneg 38, .nonneg 39, .nonneg 44, .nonneg 51, .nonneg 53, .branchLe 16 (0), .branchGe 7 (1)]

def plane461GenLeaf0002Mult : Fin 62 → Nat := ![3948, 2316, 348, 100, 1308, 1556, 7036, 18440, 9698, 9076, 284, 364, 6864, 6332, 2102, 5322, 230, 1738, 3066, 1916, 6138, 908, 8144, 1442, 2510, 1777, 9079, 5587, 5751, 2062, 2599, 2253, 2222, 1326, 1530, 3103, 4889, 856, 4079, 1698, 2147, 1642, 1076, 1055, 1831, 3584, 596, 4772, 1340, 25476, 17544, 15556, 8604, 8196, 10288, 6112, 4888, 11532, 240, 24892, 25476, 37328]

theorem plane461GenLeaf0002 (x : Fin 62 → Int)
    (hroot : plane461GenOccSys.RootHolds x)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hUB_16 : x 16 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane461GenLeaf0002Refs i).resolveCoeff plane461GenOccSys j)
    (fun i => (plane461GenLeaf0002Refs i).resolveRhs plane461GenOccSys) plane461GenLeaf0002Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane461GenLeaf0002Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 11
  · exact hroot.hOcc 13
  · exact hroot.hOcc 18
  · exact hroot.hOcc 19
  · exact hroot.hOcc 25
  · exact hroot.hOcc 26
  · exact hroot.hOcc 29
  · exact hroot.hOcc 30
  · exact hroot.hOcc 33
  · exact hroot.hOcc 34
  · exact hroot.hOcc 36
  · exact hroot.hOcc 38
  · exact hroot.hOcc 40
  · exact hroot.hOcc 41
  · exact hroot.hOcc 42
  · exact hroot.hOcc 43
  · exact hroot.hOcc 44
  · exact hroot.hOcc 46
  · exact hroot.hOcc 51
  · exact hroot.hOcc 53
  · exact hroot.hOcc 57
  · exact hroot.hOcc 58
  · exact hroot.hOcc 70
  · exact hroot.hOcc 82
  · exact hroot.hOcc 86
  · exact hroot.hOcc 87
  · exact hroot.hOcc 89
  · exact hroot.hOcc 90
  · exact hroot.hOcc 91
  · exact hroot.hOcc 94
  · exact hroot.hOcc 95
  · exact hroot.hOcc 96
  · exact hroot.hOcc 98
  · exact hroot.hOcc 99
  · exact hroot.hOcc 100
  · exact hroot.hOcc 102
  · exact hroot.hOcc 103
  · exact hroot.hOcc 107
  · exact hroot.hOcc 109
  · exact hroot.hOcc 110
  · exact hroot.hOcc 112
  · exact hroot.hOcc 114
  · exact hroot.hOcc 117
  · exact hroot.hOcc 126
  · exact hroot.hOcc 131
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 148
  · exact hroot.hOcc 150
  · change (∑ j, (-1 : Int) * x j) ≤ -plane461GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (9 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 9
  · change (∑ k, (if k = (32 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (33 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (36 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (38 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (39 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (44 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (51 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 51
  · change (∑ k, (if k = (53 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (16 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (7 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7

end QiushiMatmul
