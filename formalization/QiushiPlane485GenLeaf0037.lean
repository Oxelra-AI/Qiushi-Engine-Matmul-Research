import QiushiPlane485GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane485GenLeaf0037Refs : Fin 36 → RowRef 421 41 := ![.occ 101, .occ 102, .occ 114, .occ 134, .occ 135, .occ 136, .occ 139, .occ 147, .occ 148, .occ 149, .occ 164, .occ 171, .occ 173, .occ 176, .occ 184, .occ 239, .occ 245, .occ 256, .occ 258, .occ 279, .occ 292, .occ 298, .occ 340, .occ 356, .occ 368, .occ 369, .occ 385, .occ 386, .occ 391, .occ 414, .sumGe, .nonneg 0, .branchGe 28 (1), .branchLe 19 (0), .branchGe 22 (1), .branchGe 6 (1)]

def plane485GenLeaf0037Mult : Fin 36 → Nat := ![388, 454, 306, 241, 235, 556, 63, 34, 454, 544, 58, 68, 206, 554, 770, 760, 350, 198, 141, 1144, 148, 204, 282, 34, 8, 92, 56, 382, 932, 34, 1348, 736, 3188, 1292, 4966, 2190]

theorem plane485GenLeaf0037 (x : Fin 41 → Int)
    (hroot : plane485GenOccSys.RootHolds x)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hUB_19 : x 19 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane485GenLeaf0037Refs i).resolveCoeff plane485GenOccSys j)
    (fun i => (plane485GenLeaf0037Refs i).resolveRhs plane485GenOccSys) plane485GenLeaf0037Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane485GenLeaf0037Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 101
  · exact hroot.hOcc 102
  · exact hroot.hOcc 114
  · exact hroot.hOcc 134
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 139
  · exact hroot.hOcc 147
  · exact hroot.hOcc 148
  · exact hroot.hOcc 149
  · exact hroot.hOcc 164
  · exact hroot.hOcc 171
  · exact hroot.hOcc 173
  · exact hroot.hOcc 176
  · exact hroot.hOcc 184
  · exact hroot.hOcc 239
  · exact hroot.hOcc 245
  · exact hroot.hOcc 256
  · exact hroot.hOcc 258
  · exact hroot.hOcc 279
  · exact hroot.hOcc 292
  · exact hroot.hOcc 298
  · exact hroot.hOcc 340
  · exact hroot.hOcc 356
  · exact hroot.hOcc 368
  · exact hroot.hOcc 369
  · exact hroot.hOcc 385
  · exact hroot.hOcc 386
  · exact hroot.hOcc 391
  · exact hroot.hOcc 414
  · change (∑ j, (-1 : Int) * x j) ≤ -plane485GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (28 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (19 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (22 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22
  · change (∑ k, (if k = (6 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6

end QiushiMatmul
