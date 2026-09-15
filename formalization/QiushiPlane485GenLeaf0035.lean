import QiushiPlane485GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane485GenLeaf0035Refs : Fin 40 → RowRef 421 41 := ![.occ 91, .occ 106, .occ 111, .occ 122, .occ 126, .occ 132, .occ 133, .occ 134, .occ 137, .occ 141, .occ 142, .occ 155, .occ 162, .occ 169, .occ 178, .occ 184, .occ 185, .occ 190, .occ 195, .occ 205, .occ 206, .occ 207, .occ 210, .occ 229, .occ 230, .occ 243, .occ 245, .occ 265, .occ 286, .occ 287, .occ 301, .occ 316, .occ 362, .occ 395, .sumGe, .nonneg 7, .branchGe 28 (1), .branchLe 19 (0), .branchLe 22 (0), .branchGe 0 (1)]

def plane485GenLeaf0035Mult : Fin 40 → Nat := ![260, 80, 128, 122, 40, 85, 102, 201, 17, 195, 204, 128, 36, 136, 184, 77, 225, 67, 217, 245, 42, 109, 60, 103, 157, 286, 34, 36, 170, 170, 20, 34, 17, 57, 490, 62, 796, 144, 346, 2758]

theorem plane485GenLeaf0035 (x : Fin 41 → Int)
    (hroot : plane485GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane485GenLeaf0035Refs i).resolveCoeff plane485GenOccSys j)
    (fun i => (plane485GenLeaf0035Refs i).resolveRhs plane485GenOccSys) plane485GenLeaf0035Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane485GenLeaf0035Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 91
  · exact hroot.hOcc 106
  · exact hroot.hOcc 111
  · exact hroot.hOcc 122
  · exact hroot.hOcc 126
  · exact hroot.hOcc 132
  · exact hroot.hOcc 133
  · exact hroot.hOcc 134
  · exact hroot.hOcc 137
  · exact hroot.hOcc 141
  · exact hroot.hOcc 142
  · exact hroot.hOcc 155
  · exact hroot.hOcc 162
  · exact hroot.hOcc 169
  · exact hroot.hOcc 178
  · exact hroot.hOcc 184
  · exact hroot.hOcc 185
  · exact hroot.hOcc 190
  · exact hroot.hOcc 195
  · exact hroot.hOcc 205
  · exact hroot.hOcc 206
  · exact hroot.hOcc 207
  · exact hroot.hOcc 210
  · exact hroot.hOcc 229
  · exact hroot.hOcc 230
  · exact hroot.hOcc 243
  · exact hroot.hOcc 245
  · exact hroot.hOcc 265
  · exact hroot.hOcc 286
  · exact hroot.hOcc 287
  · exact hroot.hOcc 301
  · exact hroot.hOcc 316
  · exact hroot.hOcc 362
  · exact hroot.hOcc 395
  · change (∑ j, (-1 : Int) * x j) ≤ -plane485GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (28 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (19 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (22 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (0 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
