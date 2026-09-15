import QiushiPlane427GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane427GenLeaf0001Refs : Fin 51 → RowRef 237 50 := ![.occ 7, .occ 8, .occ 9, .occ 15, .occ 19, .occ 20, .occ 27, .occ 37, .occ 38, .occ 44, .occ 47, .occ 52, .occ 56, .occ 59, .occ 65, .occ 83, .occ 102, .occ 112, .occ 127, .occ 136, .occ 139, .occ 148, .occ 160, .occ 163, .occ 169, .occ 174, .occ 175, .occ 176, .occ 180, .occ 181, .occ 187, .occ 200, .occ 206, .occ 207, .occ 209, .occ 211, .occ 230, .occ 231, .occ 235, .sumGe, .nonneg 16, .nonneg 24, .nonneg 38, .nonneg 41, .nonneg 49, .branchLe 26 (0), .branchLe 15 (0), .branchLe 35 (0), .branchLe 45 (0), .branchLe 18 (0), .branchGe 28 (1)]

def plane427GenLeaf0001Mult : Fin 51 → Nat := ![19555, 32045, 18398, 3267, 811, 2235, 3279, 14381, 4002, 25234, 3016, 18058, 2532, 16648, 17906, 7616, 770, 9815, 19380, 17800, 146, 9951, 13235, 3266, 2496, 1196, 11397, 8518, 13344, 767, 10716, 16487, 7090, 22506, 9927, 3158, 1305, 3641, 6560, 51709, 19160, 11360, 24938, 20425, 3248, 37727, 13595, 23186, 44805, 44910, 86031]

theorem plane427GenLeaf0001 (x : Fin 50 → Int)
    (hroot : plane427GenOccSys.RootHolds x)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    (hUB_45 : x 45 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane427GenLeaf0001Refs i).resolveCoeff plane427GenOccSys j)
    (fun i => (plane427GenLeaf0001Refs i).resolveRhs plane427GenOccSys) plane427GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane427GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 7
  · exact hroot.hOcc 8
  · exact hroot.hOcc 9
  · exact hroot.hOcc 15
  · exact hroot.hOcc 19
  · exact hroot.hOcc 20
  · exact hroot.hOcc 27
  · exact hroot.hOcc 37
  · exact hroot.hOcc 38
  · exact hroot.hOcc 44
  · exact hroot.hOcc 47
  · exact hroot.hOcc 52
  · exact hroot.hOcc 56
  · exact hroot.hOcc 59
  · exact hroot.hOcc 65
  · exact hroot.hOcc 83
  · exact hroot.hOcc 102
  · exact hroot.hOcc 112
  · exact hroot.hOcc 127
  · exact hroot.hOcc 136
  · exact hroot.hOcc 139
  · exact hroot.hOcc 148
  · exact hroot.hOcc 160
  · exact hroot.hOcc 163
  · exact hroot.hOcc 169
  · exact hroot.hOcc 174
  · exact hroot.hOcc 175
  · exact hroot.hOcc 176
  · exact hroot.hOcc 180
  · exact hroot.hOcc 181
  · exact hroot.hOcc 187
  · exact hroot.hOcc 200
  · exact hroot.hOcc 206
  · exact hroot.hOcc 207
  · exact hroot.hOcc 209
  · exact hroot.hOcc 211
  · exact hroot.hOcc 230
  · exact hroot.hOcc 231
  · exact hroot.hOcc 235
  · change (∑ j, (-1 : Int) * x j) ≤ -plane427GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (16 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (24 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (38 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (41 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (49 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (26 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (15 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (35 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (45 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_45
  · change (∑ k, (if k = (18 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (28 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28

end QiushiMatmul
