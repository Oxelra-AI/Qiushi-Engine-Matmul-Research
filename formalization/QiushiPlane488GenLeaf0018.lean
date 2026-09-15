import QiushiPlane488GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane488GenLeaf0018Refs : Fin 42 → RowRef 413 41 := ![.occ 86, .occ 110, .occ 141, .occ 143, .occ 156, .occ 183, .occ 189, .occ 203, .occ 214, .occ 217, .occ 218, .occ 233, .occ 241, .occ 246, .occ 250, .occ 251, .occ 265, .occ 272, .occ 278, .occ 292, .occ 304, .occ 317, .occ 333, .occ 338, .occ 348, .occ 356, .occ 361, .occ 366, .occ 371, .occ 388, .occ 395, .occ 397, .occ 401, .occ 404, .sumGe, .nonneg 0, .nonneg 13, .branchLe 27 (0), .branchGe 15 (1), .branchLe 14 (0), .branchLe 24 (0), .branchLe 25 (0)]

def plane488GenLeaf0018Mult : Fin 42 → Nat := ![440740, 1246924, 11320, 65915, 883101, 284651, 1105878, 201933, 310632, 38027, 136000, 390045, 38663, 72843, 47065, 656188, 246747, 178082, 73446, 427995, 90194, 689693, 305051, 4143, 68514, 88693, 378158, 45284, 636, 329733, 8644, 157931, 75332, 73309, 1473118, 1520361, 170825, 1315187, 5889682, 581373, 696271, 1029777]

theorem plane488GenLeaf0018 (x : Fin 41 → Int)
    (hroot : plane488GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane488GenLeaf0018Refs i).resolveCoeff plane488GenOccSys j)
    (fun i => (plane488GenLeaf0018Refs i).resolveRhs plane488GenOccSys) plane488GenLeaf0018Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane488GenLeaf0018Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 86
  · exact hroot.hOcc 110
  · exact hroot.hOcc 141
  · exact hroot.hOcc 143
  · exact hroot.hOcc 156
  · exact hroot.hOcc 183
  · exact hroot.hOcc 189
  · exact hroot.hOcc 203
  · exact hroot.hOcc 214
  · exact hroot.hOcc 217
  · exact hroot.hOcc 218
  · exact hroot.hOcc 233
  · exact hroot.hOcc 241
  · exact hroot.hOcc 246
  · exact hroot.hOcc 250
  · exact hroot.hOcc 251
  · exact hroot.hOcc 265
  · exact hroot.hOcc 272
  · exact hroot.hOcc 278
  · exact hroot.hOcc 292
  · exact hroot.hOcc 304
  · exact hroot.hOcc 317
  · exact hroot.hOcc 333
  · exact hroot.hOcc 338
  · exact hroot.hOcc 348
  · exact hroot.hOcc 356
  · exact hroot.hOcc 361
  · exact hroot.hOcc 366
  · exact hroot.hOcc 371
  · exact hroot.hOcc 388
  · exact hroot.hOcc 395
  · exact hroot.hOcc 397
  · exact hroot.hOcc 401
  · exact hroot.hOcc 404
  · change (∑ j, (-1 : Int) * x j) ≤ -plane488GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (13 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (27 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (15 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (14 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (24 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (25 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25

end QiushiMatmul
