import QiushiPlane462GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane462GenLeaf0001Refs : Fin 63 → RowRef 294 62 := ![.occ 1, .occ 3, .occ 9, .occ 29, .occ 40, .occ 74, .occ 78, .occ 80, .occ 81, .occ 85, .occ 88, .occ 89, .occ 91, .occ 92, .occ 93, .occ 97, .occ 100, .occ 102, .occ 107, .occ 112, .occ 113, .occ 114, .occ 115, .occ 120, .occ 122, .occ 138, .occ 146, .occ 148, .occ 153, .occ 159, .occ 160, .occ 164, .occ 168, .occ 180, .occ 189, .occ 193, .occ 194, .occ 200, .occ 210, .occ 220, .occ 225, .occ 235, .occ 250, .occ 252, .occ 254, .occ 257, .occ 273, .occ 275, .occ 278, .occ 284, .occ 288, .sumGe, .nonneg 8, .nonneg 17, .nonneg 37, .nonneg 39, .nonneg 40, .nonneg 41, .branchLe 3 (0), .branchLe 34 (1), .branchGe 28 (1), .branchLe 43 (0), .branchLe 2 (0)]

def plane462GenLeaf0001Mult : Fin 63 → Nat := ![8176, 29568, 18872, 24260, 31236, 28156, 27996, 14788, 25424, 40052, 16260, 44584, 9488, 33044, 4480, 29792, 38388, 37436, 12992, 6392, 30062, 18150, 7270, 13739, 912, 11522, 7524, 8702, 16900, 31359, 3904, 12723, 5449, 14874, 21414, 21802, 6730, 8326, 15334, 11486, 11334, 33522, 6182, 26288, 12380, 4312, 16403, 45061, 21857, 27627, 30284, 209664, 85008, 38528, 68544, 84624, 55376, 38304, 209664, 179536, 209664, 110992, 169344]

theorem plane462GenLeaf0001 (x : Fin 62 → Int)
    (hroot : plane462GenOccSys.RootHolds x)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (1 : Int))
    (hUB_43 : x 43 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane462GenLeaf0001Refs i).resolveCoeff plane462GenOccSys j)
    (fun i => (plane462GenLeaf0001Refs i).resolveRhs plane462GenOccSys) plane462GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane462GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · exact hroot.hOcc 3
  · exact hroot.hOcc 9
  · exact hroot.hOcc 29
  · exact hroot.hOcc 40
  · exact hroot.hOcc 74
  · exact hroot.hOcc 78
  · exact hroot.hOcc 80
  · exact hroot.hOcc 81
  · exact hroot.hOcc 85
  · exact hroot.hOcc 88
  · exact hroot.hOcc 89
  · exact hroot.hOcc 91
  · exact hroot.hOcc 92
  · exact hroot.hOcc 93
  · exact hroot.hOcc 97
  · exact hroot.hOcc 100
  · exact hroot.hOcc 102
  · exact hroot.hOcc 107
  · exact hroot.hOcc 112
  · exact hroot.hOcc 113
  · exact hroot.hOcc 114
  · exact hroot.hOcc 115
  · exact hroot.hOcc 120
  · exact hroot.hOcc 122
  · exact hroot.hOcc 138
  · exact hroot.hOcc 146
  · exact hroot.hOcc 148
  · exact hroot.hOcc 153
  · exact hroot.hOcc 159
  · exact hroot.hOcc 160
  · exact hroot.hOcc 164
  · exact hroot.hOcc 168
  · exact hroot.hOcc 180
  · exact hroot.hOcc 189
  · exact hroot.hOcc 193
  · exact hroot.hOcc 194
  · exact hroot.hOcc 200
  · exact hroot.hOcc 210
  · exact hroot.hOcc 220
  · exact hroot.hOcc 225
  · exact hroot.hOcc 235
  · exact hroot.hOcc 250
  · exact hroot.hOcc 252
  · exact hroot.hOcc 254
  · exact hroot.hOcc 257
  · exact hroot.hOcc 273
  · exact hroot.hOcc 275
  · exact hroot.hOcc 278
  · exact hroot.hOcc 284
  · exact hroot.hOcc 288
  · change (∑ j, (-1 : Int) * x j) ≤ -plane462GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (17 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (37 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (39 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (40 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (41 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (3 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (34 : Fin 62) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (28 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (43 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (2 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2

end QiushiMatmul
