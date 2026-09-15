import QiushiPlane485GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane485GenLeaf0013Refs : Fin 42 → RowRef 421 41 := ![.occ 87, .occ 97, .occ 136, .occ 137, .occ 155, .occ 163, .occ 168, .occ 182, .occ 189, .occ 213, .occ 218, .occ 226, .occ 233, .occ 262, .occ 265, .occ 274, .occ 286, .occ 287, .occ 304, .occ 317, .occ 328, .occ 337, .occ 344, .occ 350, .occ 355, .occ 356, .occ 359, .occ 362, .occ 364, .occ 372, .occ 374, .occ 376, .occ 393, .occ 406, .occ 409, .occ 420, .sumGe, .branchLe 28 (0), .branchLe 21 (0), .branchLe 14 (0), .branchGe 11 (1), .branchGe 40 (1)]

def plane485GenLeaf0013Mult : Fin 42 → Nat := ![382675, 34680, 376543, 253528, 36022, 33638, 258921, 32556, 64392, 34835, 101, 120514, 198002, 434688, 447291, 103366, 194064, 489374, 1082, 11654, 191425, 25763, 143459, 57976, 17983, 139833, 20461, 325392, 19220, 6118, 16285, 647, 22669, 14781, 34835, 9054, 751183, 735654, 686791, 751183, 971779, 1720309]

theorem plane485GenLeaf0013 (x : Fin 41 → Int)
    (hroot : plane485GenOccSys.RootHolds x)
    (hLB_40 : (1 : Int) ≤ x 40)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane485GenLeaf0013Refs i).resolveCoeff plane485GenOccSys j)
    (fun i => (plane485GenLeaf0013Refs i).resolveRhs plane485GenOccSys) plane485GenLeaf0013Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane485GenLeaf0013Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 97
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 155
  · exact hroot.hOcc 163
  · exact hroot.hOcc 168
  · exact hroot.hOcc 182
  · exact hroot.hOcc 189
  · exact hroot.hOcc 213
  · exact hroot.hOcc 218
  · exact hroot.hOcc 226
  · exact hroot.hOcc 233
  · exact hroot.hOcc 262
  · exact hroot.hOcc 265
  · exact hroot.hOcc 274
  · exact hroot.hOcc 286
  · exact hroot.hOcc 287
  · exact hroot.hOcc 304
  · exact hroot.hOcc 317
  · exact hroot.hOcc 328
  · exact hroot.hOcc 337
  · exact hroot.hOcc 344
  · exact hroot.hOcc 350
  · exact hroot.hOcc 355
  · exact hroot.hOcc 356
  · exact hroot.hOcc 359
  · exact hroot.hOcc 362
  · exact hroot.hOcc 364
  · exact hroot.hOcc 372
  · exact hroot.hOcc 374
  · exact hroot.hOcc 376
  · exact hroot.hOcc 393
  · exact hroot.hOcc 406
  · exact hroot.hOcc 409
  · exact hroot.hOcc 420
  · change (∑ j, (-1 : Int) * x j) ≤ -plane485GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (28 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (21 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (14 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (11 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11
  · change (∑ k, (if k = (40 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_40

end QiushiMatmul
