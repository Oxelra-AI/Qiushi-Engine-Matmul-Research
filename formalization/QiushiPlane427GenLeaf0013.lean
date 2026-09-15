import QiushiPlane427GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane427GenLeaf0013Refs : Fin 51 → RowRef 237 50 := ![.occ 8, .occ 10, .occ 15, .occ 20, .occ 27, .occ 35, .occ 36, .occ 40, .occ 42, .occ 43, .occ 47, .occ 56, .occ 60, .occ 68, .occ 88, .occ 105, .occ 114, .occ 118, .occ 129, .occ 134, .occ 149, .occ 150, .occ 153, .occ 155, .occ 158, .occ 161, .occ 166, .occ 167, .occ 169, .occ 176, .occ 180, .occ 182, .occ 184, .occ 189, .occ 204, .occ 205, .occ 208, .occ 209, .sumGe, .nonneg 5, .nonneg 13, .nonneg 16, .nonneg 20, .nonneg 27, .nonneg 39, .nonneg 44, .nonneg 46, .branchGe 26 (1), .branchLe 14 (0), .branchLe 48 (0), .branchLe 35 (0)]

def plane427GenLeaf0013Mult : Fin 51 → Nat := ![39015, 22365, 11658, 17157, 4374, 14290, 13781, 6696, 21108, 3215, 2136, 8043, 24429, 10692, 2328, 4567, 2466, 175, 24542, 7586, 5067, 2121, 5328, 12966, 8832, 21021, 310, 7615, 2596, 11054, 7847, 8043, 10989, 375, 10887, 8157, 10134, 18669, 47847, 11250, 6360, 16974, 26088, 1080, 29610, 18013, 28058, 125463, 33948, 47472, 47472]

theorem plane427GenLeaf0013 (x : Fin 50 → Int)
    (hroot : plane427GenOccSys.RootHolds x)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_48 : x 48 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane427GenLeaf0013Refs i).resolveCoeff plane427GenOccSys j)
    (fun i => (plane427GenLeaf0013Refs i).resolveRhs plane427GenOccSys) plane427GenLeaf0013Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane427GenLeaf0013Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 8
  · exact hroot.hOcc 10
  · exact hroot.hOcc 15
  · exact hroot.hOcc 20
  · exact hroot.hOcc 27
  · exact hroot.hOcc 35
  · exact hroot.hOcc 36
  · exact hroot.hOcc 40
  · exact hroot.hOcc 42
  · exact hroot.hOcc 43
  · exact hroot.hOcc 47
  · exact hroot.hOcc 56
  · exact hroot.hOcc 60
  · exact hroot.hOcc 68
  · exact hroot.hOcc 88
  · exact hroot.hOcc 105
  · exact hroot.hOcc 114
  · exact hroot.hOcc 118
  · exact hroot.hOcc 129
  · exact hroot.hOcc 134
  · exact hroot.hOcc 149
  · exact hroot.hOcc 150
  · exact hroot.hOcc 153
  · exact hroot.hOcc 155
  · exact hroot.hOcc 158
  · exact hroot.hOcc 161
  · exact hroot.hOcc 166
  · exact hroot.hOcc 167
  · exact hroot.hOcc 169
  · exact hroot.hOcc 176
  · exact hroot.hOcc 180
  · exact hroot.hOcc 182
  · exact hroot.hOcc 184
  · exact hroot.hOcc 189
  · exact hroot.hOcc 204
  · exact hroot.hOcc 205
  · exact hroot.hOcc 208
  · exact hroot.hOcc 209
  · change (∑ j, (-1 : Int) * x j) ≤ -plane427GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (5 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (13 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (16 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (20 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (27 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27
  · change (∑ k, (if k = (39 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (44 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (46 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (26 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (14 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (48 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_48
  · change (∑ k, (if k = (35 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35

end QiushiMatmul
