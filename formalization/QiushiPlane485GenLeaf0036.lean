import QiushiPlane485GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane485GenLeaf0036Refs : Fin 39 → RowRef 421 41 := ![.occ 87, .occ 101, .occ 102, .occ 122, .occ 132, .occ 133, .occ 140, .occ 148, .occ 149, .occ 150, .occ 164, .occ 171, .occ 173, .occ 176, .occ 182, .occ 184, .occ 190, .occ 197, .occ 217, .occ 239, .occ 243, .occ 245, .occ 260, .occ 262, .occ 265, .occ 279, .occ 283, .occ 287, .occ 344, .occ 352, .occ 356, .occ 376, .occ 382, .occ 414, .sumGe, .branchGe 28 (1), .branchLe 19 (0), .branchGe 22 (1), .branchLe 6 (0)]

def plane485GenLeaf0036Mult : Fin 39 → Nat := ![19566, 30716, 24863, 36408, 935, 8079, 17774, 19840, 18481, 13820, 5991, 7902, 29154, 20519, 14752, 10501, 20669, 11500, 932, 15117, 6215, 2619, 39255, 3392, 1864, 33027, 1684, 932, 1254, 11810, 2644, 16314, 13372, 7497, 61151, 117782, 36470, 248690, 59467]

theorem plane485GenLeaf0036 (x : Fin 41 → Int)
    (hroot : plane485GenOccSys.RootHolds x)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane485GenLeaf0036Refs i).resolveCoeff plane485GenOccSys j)
    (fun i => (plane485GenLeaf0036Refs i).resolveRhs plane485GenOccSys) plane485GenLeaf0036Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane485GenLeaf0036Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 101
  · exact hroot.hOcc 102
  · exact hroot.hOcc 122
  · exact hroot.hOcc 132
  · exact hroot.hOcc 133
  · exact hroot.hOcc 140
  · exact hroot.hOcc 148
  · exact hroot.hOcc 149
  · exact hroot.hOcc 150
  · exact hroot.hOcc 164
  · exact hroot.hOcc 171
  · exact hroot.hOcc 173
  · exact hroot.hOcc 176
  · exact hroot.hOcc 182
  · exact hroot.hOcc 184
  · exact hroot.hOcc 190
  · exact hroot.hOcc 197
  · exact hroot.hOcc 217
  · exact hroot.hOcc 239
  · exact hroot.hOcc 243
  · exact hroot.hOcc 245
  · exact hroot.hOcc 260
  · exact hroot.hOcc 262
  · exact hroot.hOcc 265
  · exact hroot.hOcc 279
  · exact hroot.hOcc 283
  · exact hroot.hOcc 287
  · exact hroot.hOcc 344
  · exact hroot.hOcc 352
  · exact hroot.hOcc 356
  · exact hroot.hOcc 376
  · exact hroot.hOcc 382
  · exact hroot.hOcc 414
  · change (∑ j, (-1 : Int) * x j) ≤ -plane485GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (28 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (19 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (22 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22
  · change (∑ k, (if k = (6 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6

end QiushiMatmul
