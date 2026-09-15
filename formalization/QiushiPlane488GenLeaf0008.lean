import QiushiPlane488GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane488GenLeaf0008Refs : Fin 42 → RowRef 413 41 := ![.occ 91, .occ 100, .occ 102, .occ 112, .occ 127, .occ 139, .occ 140, .occ 174, .occ 187, .occ 190, .occ 203, .occ 212, .occ 216, .occ 219, .occ 225, .occ 226, .occ 236, .occ 241, .occ 257, .occ 261, .occ 265, .occ 270, .occ 274, .occ 277, .occ 308, .occ 339, .occ 362, .occ 368, .occ 381, .occ 383, .occ 384, .occ 402, .occ 403, .occ 411, .sumGe, .branchLe 27 (0), .branchLe 15 (0), .branchLe 20 (0), .branchGe 25 (1), .branchLe 1 (0), .branchLe 6 (0), .branchLe 3 (0)]

def plane488GenLeaf0008Mult : Fin 42 → Nat := ![3477, 1032, 998, 1678, 3445, 1310, 6482, 1122, 856, 1296, 1228, 3088, 2226, 3026, 1726, 1376, 864, 1071, 1662, 458, 3615, 383, 1141, 1515, 285, 119, 26, 1062, 2817, 1177, 1898, 1607, 536, 51, 8625, 3359, 5599, 6682, 20886, 8599, 7278, 7278]

theorem plane488GenLeaf0008 (x : Fin 41 → Int)
    (hroot : plane488GenOccSys.RootHolds x)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane488GenLeaf0008Refs i).resolveCoeff plane488GenOccSys j)
    (fun i => (plane488GenLeaf0008Refs i).resolveRhs plane488GenOccSys) plane488GenLeaf0008Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane488GenLeaf0008Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 91
  · exact hroot.hOcc 100
  · exact hroot.hOcc 102
  · exact hroot.hOcc 112
  · exact hroot.hOcc 127
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 174
  · exact hroot.hOcc 187
  · exact hroot.hOcc 190
  · exact hroot.hOcc 203
  · exact hroot.hOcc 212
  · exact hroot.hOcc 216
  · exact hroot.hOcc 219
  · exact hroot.hOcc 225
  · exact hroot.hOcc 226
  · exact hroot.hOcc 236
  · exact hroot.hOcc 241
  · exact hroot.hOcc 257
  · exact hroot.hOcc 261
  · exact hroot.hOcc 265
  · exact hroot.hOcc 270
  · exact hroot.hOcc 274
  · exact hroot.hOcc 277
  · exact hroot.hOcc 308
  · exact hroot.hOcc 339
  · exact hroot.hOcc 362
  · exact hroot.hOcc 368
  · exact hroot.hOcc 381
  · exact hroot.hOcc 383
  · exact hroot.hOcc 384
  · exact hroot.hOcc 402
  · exact hroot.hOcc 403
  · exact hroot.hOcc 411
  · change (∑ j, (-1 : Int) * x j) ≤ -plane488GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (27 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (15 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (20 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (25 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25
  · change (∑ k, (if k = (1 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (6 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (3 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3

end QiushiMatmul
