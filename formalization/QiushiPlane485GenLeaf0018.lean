import QiushiPlane485GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane485GenLeaf0018Refs : Fin 42 → RowRef 421 41 := ![.occ 87, .occ 94, .occ 95, .occ 133, .occ 135, .occ 136, .occ 137, .occ 154, .occ 177, .occ 179, .occ 184, .occ 195, .occ 207, .occ 228, .occ 233, .occ 238, .occ 246, .occ 250, .occ 252, .occ 257, .occ 262, .occ 273, .occ 287, .occ 294, .occ 302, .occ 305, .occ 328, .occ 353, .occ 354, .occ 366, .occ 375, .occ 394, .occ 408, .occ 419, .sumGe, .nonneg 0, .branchLe 28 (0), .branchLe 21 (0), .branchGe 14 (1), .branchLe 29 (0), .branchGe 13 (1), .branchLe 1 (0)]

def plane485GenLeaf0018Mult : Fin 42 → Nat := ![16703, 5726, 12151, 5854, 10944, 25212, 13607, 683, 17, 14140, 52686, 18733, 25186, 18675, 29637, 180, 22166, 6166, 27060, 21919, 6713, 12153, 11649, 5035, 9468, 1273, 13664, 6951, 255, 5458, 2923, 20726, 2923, 2445, 66350, 126026, 66170, 19969, 119048, 11624, 166179, 54723]

theorem plane485GenLeaf0018 (x : Fin 41 → Int)
    (hroot : plane485GenOccSys.RootHolds x)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane485GenLeaf0018Refs i).resolveCoeff plane485GenOccSys j)
    (fun i => (plane485GenLeaf0018Refs i).resolveRhs plane485GenOccSys) plane485GenLeaf0018Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane485GenLeaf0018Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 94
  · exact hroot.hOcc 95
  · exact hroot.hOcc 133
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 154
  · exact hroot.hOcc 177
  · exact hroot.hOcc 179
  · exact hroot.hOcc 184
  · exact hroot.hOcc 195
  · exact hroot.hOcc 207
  · exact hroot.hOcc 228
  · exact hroot.hOcc 233
  · exact hroot.hOcc 238
  · exact hroot.hOcc 246
  · exact hroot.hOcc 250
  · exact hroot.hOcc 252
  · exact hroot.hOcc 257
  · exact hroot.hOcc 262
  · exact hroot.hOcc 273
  · exact hroot.hOcc 287
  · exact hroot.hOcc 294
  · exact hroot.hOcc 302
  · exact hroot.hOcc 305
  · exact hroot.hOcc 328
  · exact hroot.hOcc 353
  · exact hroot.hOcc 354
  · exact hroot.hOcc 366
  · exact hroot.hOcc 375
  · exact hroot.hOcc 394
  · exact hroot.hOcc 408
  · exact hroot.hOcc 419
  · change (∑ j, (-1 : Int) * x j) ≤ -plane485GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (28 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (21 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (14 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (29 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (13 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13
  · change (∑ k, (if k = (1 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1

end QiushiMatmul
