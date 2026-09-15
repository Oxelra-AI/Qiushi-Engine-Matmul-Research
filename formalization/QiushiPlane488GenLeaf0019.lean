import QiushiPlane488GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane488GenLeaf0019Refs : Fin 41 → RowRef 413 41 := ![.occ 90, .occ 100, .occ 107, .occ 110, .occ 127, .occ 137, .occ 146, .occ 156, .occ 159, .occ 160, .occ 161, .occ 170, .occ 183, .occ 189, .occ 195, .occ 209, .occ 210, .occ 219, .occ 226, .occ 241, .occ 247, .occ 248, .occ 262, .occ 265, .occ 272, .occ 288, .occ 297, .occ 304, .occ 317, .occ 319, .occ 335, .occ 357, .occ 377, .occ 391, .occ 397, .sumGe, .nonneg 0, .branchGe 15 (1), .branchLe 14 (0), .branchLe 24 (0), .branchGe 25 (1)]

def plane488GenLeaf0019Mult : Fin 41 → Nat := ![677, 630, 2395, 506, 3039, 596, 4599, 2970, 1140, 1066, 888, 613, 2259, 1777, 1756, 846, 383, 577, 833, 2292, 1066, 1559, 757, 1146, 527, 1263, 119, 21, 506, 323, 479, 1305, 323, 743, 705, 5176, 573, 16503, 1373, 5176, 17255]

theorem plane488GenLeaf0019 (x : Fin 41 → Int)
    (hroot : plane488GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane488GenLeaf0019Refs i).resolveCoeff plane488GenOccSys j)
    (fun i => (plane488GenLeaf0019Refs i).resolveRhs plane488GenOccSys) plane488GenLeaf0019Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane488GenLeaf0019Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 90
  · exact hroot.hOcc 100
  · exact hroot.hOcc 107
  · exact hroot.hOcc 110
  · exact hroot.hOcc 127
  · exact hroot.hOcc 137
  · exact hroot.hOcc 146
  · exact hroot.hOcc 156
  · exact hroot.hOcc 159
  · exact hroot.hOcc 160
  · exact hroot.hOcc 161
  · exact hroot.hOcc 170
  · exact hroot.hOcc 183
  · exact hroot.hOcc 189
  · exact hroot.hOcc 195
  · exact hroot.hOcc 209
  · exact hroot.hOcc 210
  · exact hroot.hOcc 219
  · exact hroot.hOcc 226
  · exact hroot.hOcc 241
  · exact hroot.hOcc 247
  · exact hroot.hOcc 248
  · exact hroot.hOcc 262
  · exact hroot.hOcc 265
  · exact hroot.hOcc 272
  · exact hroot.hOcc 288
  · exact hroot.hOcc 297
  · exact hroot.hOcc 304
  · exact hroot.hOcc 317
  · exact hroot.hOcc 319
  · exact hroot.hOcc 335
  · exact hroot.hOcc 357
  · exact hroot.hOcc 377
  · exact hroot.hOcc 391
  · exact hroot.hOcc 397
  · change (∑ j, (-1 : Int) * x j) ≤ -plane488GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (15 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (14 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (24 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (25 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25

end QiushiMatmul
