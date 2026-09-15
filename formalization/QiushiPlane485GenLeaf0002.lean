import QiushiPlane485GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane485GenLeaf0002Refs : Fin 42 → RowRef 421 41 := ![.occ 87, .occ 90, .occ 99, .occ 121, .occ 134, .occ 135, .occ 145, .occ 151, .occ 152, .occ 155, .occ 161, .occ 164, .occ 167, .occ 172, .occ 175, .occ 179, .occ 182, .occ 188, .occ 209, .occ 213, .occ 234, .occ 243, .occ 244, .occ 262, .occ 265, .occ 276, .occ 278, .occ 283, .occ 297, .occ 353, .occ 402, .occ 403, .occ 412, .sumGe, .nonneg 17, .branchLe 28 (0), .branchLe 21 (0), .branchLe 14 (0), .branchLe 11 (0), .branchLe 39 (0), .branchGe 10 (1), .branchGe 24 (1)]

def plane485GenLeaf0002Mult : Fin 42 → Nat := ![5151, 2047, 692, 52, 3671, 4738, 2029, 3070, 4407, 2969, 326, 4646, 923, 4920, 2477, 2363, 1837, 2988, 966, 3847, 295, 6688, 1093, 586, 8158, 3240, 2768, 1977, 1675, 4062, 1955, 2477, 1267, 15283, 1773, 6640, 11653, 15283, 8568, 15283, 9406, 33561]

theorem plane485GenLeaf0002 (x : Fin 41 → Int)
    (hroot : plane485GenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane485GenLeaf0002Refs i).resolveCoeff plane485GenOccSys j)
    (fun i => (plane485GenLeaf0002Refs i).resolveRhs plane485GenOccSys) plane485GenLeaf0002Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane485GenLeaf0002Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 90
  · exact hroot.hOcc 99
  · exact hroot.hOcc 121
  · exact hroot.hOcc 134
  · exact hroot.hOcc 135
  · exact hroot.hOcc 145
  · exact hroot.hOcc 151
  · exact hroot.hOcc 152
  · exact hroot.hOcc 155
  · exact hroot.hOcc 161
  · exact hroot.hOcc 164
  · exact hroot.hOcc 167
  · exact hroot.hOcc 172
  · exact hroot.hOcc 175
  · exact hroot.hOcc 179
  · exact hroot.hOcc 182
  · exact hroot.hOcc 188
  · exact hroot.hOcc 209
  · exact hroot.hOcc 213
  · exact hroot.hOcc 234
  · exact hroot.hOcc 243
  · exact hroot.hOcc 244
  · exact hroot.hOcc 262
  · exact hroot.hOcc 265
  · exact hroot.hOcc 276
  · exact hroot.hOcc 278
  · exact hroot.hOcc 283
  · exact hroot.hOcc 297
  · exact hroot.hOcc 353
  · exact hroot.hOcc 402
  · exact hroot.hOcc 403
  · exact hroot.hOcc 412
  · change (∑ j, (-1 : Int) * x j) ≤ -plane485GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (17 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (28 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (21 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (14 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (11 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (39 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (10 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10
  · change (∑ k, (if k = (24 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24

end QiushiMatmul
