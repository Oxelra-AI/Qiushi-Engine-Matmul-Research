import QiushiPlane485GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane485GenLeaf0012Refs : Fin 41 → RowRef 421 41 := ![.occ 87, .occ 93, .occ 116, .occ 135, .occ 136, .occ 137, .occ 141, .occ 142, .occ 146, .occ 148, .occ 151, .occ 152, .occ 157, .occ 173, .occ 175, .occ 179, .occ 182, .occ 184, .occ 195, .occ 207, .occ 213, .occ 227, .occ 228, .occ 233, .occ 234, .occ 239, .occ 246, .occ 257, .occ 276, .occ 278, .occ 328, .occ 356, .occ 378, .occ 411, .sumGe, .branchLe 28 (0), .branchLe 21 (0), .branchLe 14 (0), .branchGe 11 (1), .branchLe 40 (0), .branchGe 13 (1)]

def plane485GenLeaf0012Mult : Fin 41 → Nat := ![2334, 514, 2172, 2308, 845, 1041, 285, 83, 228, 1042, 462, 510, 1652, 480, 130, 578, 228, 758, 708, 522, 248, 1670, 770, 1230, 224, 1004, 1626, 534, 582, 272, 1220, 148, 582, 222, 3660, 3660, 1160, 1672, 6396, 3512, 11024]

theorem plane485GenLeaf0012 (x : Fin 41 → Int)
    (hroot : plane485GenOccSys.RootHolds x)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hUB_40 : x 40 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane485GenLeaf0012Refs i).resolveCoeff plane485GenOccSys j)
    (fun i => (plane485GenLeaf0012Refs i).resolveRhs plane485GenOccSys) plane485GenLeaf0012Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane485GenLeaf0012Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 93
  · exact hroot.hOcc 116
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 141
  · exact hroot.hOcc 142
  · exact hroot.hOcc 146
  · exact hroot.hOcc 148
  · exact hroot.hOcc 151
  · exact hroot.hOcc 152
  · exact hroot.hOcc 157
  · exact hroot.hOcc 173
  · exact hroot.hOcc 175
  · exact hroot.hOcc 179
  · exact hroot.hOcc 182
  · exact hroot.hOcc 184
  · exact hroot.hOcc 195
  · exact hroot.hOcc 207
  · exact hroot.hOcc 213
  · exact hroot.hOcc 227
  · exact hroot.hOcc 228
  · exact hroot.hOcc 233
  · exact hroot.hOcc 234
  · exact hroot.hOcc 239
  · exact hroot.hOcc 246
  · exact hroot.hOcc 257
  · exact hroot.hOcc 276
  · exact hroot.hOcc 278
  · exact hroot.hOcc 328
  · exact hroot.hOcc 356
  · exact hroot.hOcc 378
  · exact hroot.hOcc 411
  · change (∑ j, (-1 : Int) * x j) ≤ -plane485GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (28 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (21 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (14 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (11 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11
  · change (∑ k, (if k = (40 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (13 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13

end QiushiMatmul
