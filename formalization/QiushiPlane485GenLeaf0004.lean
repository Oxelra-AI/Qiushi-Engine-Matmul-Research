import QiushiPlane485GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane485GenLeaf0004Refs : Fin 42 → RowRef 421 41 := ![.occ 87, .occ 95, .occ 108, .occ 116, .occ 123, .occ 132, .occ 133, .occ 134, .occ 140, .occ 152, .occ 155, .occ 167, .occ 177, .occ 179, .occ 203, .occ 210, .occ 213, .occ 228, .occ 230, .occ 232, .occ 233, .occ 236, .occ 246, .occ 255, .occ 265, .occ 287, .occ 302, .occ 304, .occ 305, .occ 358, .occ 362, .occ 372, .sumGe, .branchLe 28 (0), .branchLe 21 (0), .branchLe 14 (0), .branchLe 11 (0), .branchGe 39 (1), .branchLe 29 (0), .branchLe 18 (0), .branchLe 26 (0), .branchLe 22 (0)]

def plane485GenLeaf0004Mult : Fin 42 → Nat := ![11977, 2961, 2841, 4431, 9620, 196, 874, 4404, 6555, 4941, 2626, 1887, 8503, 9266, 1650, 1380, 7921, 8066, 1748, 11662, 1771, 5457, 176, 4896, 1196, 5022, 1814, 3065, 695, 5167, 10206, 3159, 24750, 24750, 14867, 22936, 11385, 27329, 22803, 11138, 24055, 24750]

theorem plane485GenLeaf0004 (x : Fin 41 → Int)
    (hroot : plane485GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane485GenLeaf0004Refs i).resolveCoeff plane485GenOccSys j)
    (fun i => (plane485GenLeaf0004Refs i).resolveRhs plane485GenOccSys) plane485GenLeaf0004Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane485GenLeaf0004Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 95
  · exact hroot.hOcc 108
  · exact hroot.hOcc 116
  · exact hroot.hOcc 123
  · exact hroot.hOcc 132
  · exact hroot.hOcc 133
  · exact hroot.hOcc 134
  · exact hroot.hOcc 140
  · exact hroot.hOcc 152
  · exact hroot.hOcc 155
  · exact hroot.hOcc 167
  · exact hroot.hOcc 177
  · exact hroot.hOcc 179
  · exact hroot.hOcc 203
  · exact hroot.hOcc 210
  · exact hroot.hOcc 213
  · exact hroot.hOcc 228
  · exact hroot.hOcc 230
  · exact hroot.hOcc 232
  · exact hroot.hOcc 233
  · exact hroot.hOcc 236
  · exact hroot.hOcc 246
  · exact hroot.hOcc 255
  · exact hroot.hOcc 265
  · exact hroot.hOcc 287
  · exact hroot.hOcc 302
  · exact hroot.hOcc 304
  · exact hroot.hOcc 305
  · exact hroot.hOcc 358
  · exact hroot.hOcc 362
  · exact hroot.hOcc 372
  · change (∑ j, (-1 : Int) * x j) ≤ -plane485GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (28 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (21 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (14 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (11 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (39 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (29 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (18 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (26 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (22 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22

end QiushiMatmul
