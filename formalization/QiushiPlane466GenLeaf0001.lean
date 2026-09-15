import QiushiPlane466GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane466GenLeaf0001Refs : Fin 51 → RowRef 210 50 := ![.occ 15, .occ 24, .occ 33, .occ 49, .occ 53, .occ 58, .occ 59, .occ 60, .occ 62, .occ 63, .occ 64, .occ 65, .occ 73, .occ 79, .occ 81, .occ 83, .occ 84, .occ 100, .occ 102, .occ 103, .occ 111, .occ 118, .occ 128, .occ 129, .occ 133, .occ 135, .occ 159, .occ 160, .occ 161, .occ 166, .occ 172, .occ 178, .occ 179, .occ 187, .occ 188, .occ 197, .occ 200, .occ 205, .occ 209, .sumGe, .nonneg 0, .nonneg 16, .nonneg 38, .nonneg 39, .nonneg 44, .nonneg 46, .branchLe 24 (0), .branchLe 19 (0), .branchLe 26 (0), .branchLe 28 (0), .branchGe 7 (1)]

def plane466GenLeaf0001Mult : Fin 51 → Nat := ![1181258, 1694264, 59890, 190590, 2731518, 2844046, 1026974, 1889590, 733725, 659915, 791587, 364629, 309632, 8141, 727961, 1351695, 797821, 821584, 2229954, 665772, 995044, 2336208, 1890908, 487056, 661486, 381052, 823444, 1810612, 350840, 316926, 958614, 859576, 453656, 563366, 292344, 321260, 14408, 981876, 324804, 5006436, 2885714, 795812, 360374, 1717334, 1313134, 1505222, 3515946, 4048320, 5006436, 3025102, 16505084]

theorem plane466GenLeaf0001 (x : Fin 50 → Int)
    (hroot : plane466GenOccSys.RootHolds x)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane466GenLeaf0001Refs i).resolveCoeff plane466GenOccSys j)
    (fun i => (plane466GenLeaf0001Refs i).resolveRhs plane466GenOccSys) plane466GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane466GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 15
  · exact hroot.hOcc 24
  · exact hroot.hOcc 33
  · exact hroot.hOcc 49
  · exact hroot.hOcc 53
  · exact hroot.hOcc 58
  · exact hroot.hOcc 59
  · exact hroot.hOcc 60
  · exact hroot.hOcc 62
  · exact hroot.hOcc 63
  · exact hroot.hOcc 64
  · exact hroot.hOcc 65
  · exact hroot.hOcc 73
  · exact hroot.hOcc 79
  · exact hroot.hOcc 81
  · exact hroot.hOcc 83
  · exact hroot.hOcc 84
  · exact hroot.hOcc 100
  · exact hroot.hOcc 102
  · exact hroot.hOcc 103
  · exact hroot.hOcc 111
  · exact hroot.hOcc 118
  · exact hroot.hOcc 128
  · exact hroot.hOcc 129
  · exact hroot.hOcc 133
  · exact hroot.hOcc 135
  · exact hroot.hOcc 159
  · exact hroot.hOcc 160
  · exact hroot.hOcc 161
  · exact hroot.hOcc 166
  · exact hroot.hOcc 172
  · exact hroot.hOcc 178
  · exact hroot.hOcc 179
  · exact hroot.hOcc 187
  · exact hroot.hOcc 188
  · exact hroot.hOcc 197
  · exact hroot.hOcc 200
  · exact hroot.hOcc 205
  · exact hroot.hOcc 209
  · change (∑ j, (-1 : Int) * x j) ≤ -plane466GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (16 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (38 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (39 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (44 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (46 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (24 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (19 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (26 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (28 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (7 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7

end QiushiMatmul
