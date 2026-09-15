import QiushiPlane485GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane485GenLeaf0005Refs : Fin 42 → RowRef 421 41 := ![.occ 87, .occ 125, .occ 134, .occ 148, .occ 150, .occ 152, .occ 161, .occ 167, .occ 173, .occ 176, .occ 179, .occ 182, .occ 216, .occ 228, .occ 232, .occ 233, .occ 257, .occ 262, .occ 287, .occ 298, .occ 310, .occ 327, .occ 334, .occ 337, .occ 352, .occ 353, .occ 362, .occ 372, .occ 392, .occ 401, .occ 403, .occ 414, .sumGe, .branchLe 28 (0), .branchLe 21 (0), .branchLe 14 (0), .branchLe 11 (0), .branchGe 39 (1), .branchLe 29 (0), .branchLe 18 (0), .branchLe 26 (0), .branchGe 22 (1)]

def plane485GenLeaf0005Mult : Fin 42 → Nat := ![3637, 8220, 2165, 1579, 6459, 3066, 2292, 168, 5932, 2047, 2936, 5282, 820, 1164, 3499, 3607, 132, 1622, 1597, 3920, 412, 751, 1054, 590, 2638, 2029, 4230, 1202, 2178, 1477, 140, 4985, 16226, 11241, 4268, 16226, 10794, 7736, 11002, 15636, 3730, 33141]

theorem plane485GenLeaf0005 (x : Fin 41 → Int)
    (hroot : plane485GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane485GenLeaf0005Refs i).resolveCoeff plane485GenOccSys j)
    (fun i => (plane485GenLeaf0005Refs i).resolveRhs plane485GenOccSys) plane485GenLeaf0005Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane485GenLeaf0005Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 125
  · exact hroot.hOcc 134
  · exact hroot.hOcc 148
  · exact hroot.hOcc 150
  · exact hroot.hOcc 152
  · exact hroot.hOcc 161
  · exact hroot.hOcc 167
  · exact hroot.hOcc 173
  · exact hroot.hOcc 176
  · exact hroot.hOcc 179
  · exact hroot.hOcc 182
  · exact hroot.hOcc 216
  · exact hroot.hOcc 228
  · exact hroot.hOcc 232
  · exact hroot.hOcc 233
  · exact hroot.hOcc 257
  · exact hroot.hOcc 262
  · exact hroot.hOcc 287
  · exact hroot.hOcc 298
  · exact hroot.hOcc 310
  · exact hroot.hOcc 327
  · exact hroot.hOcc 334
  · exact hroot.hOcc 337
  · exact hroot.hOcc 352
  · exact hroot.hOcc 353
  · exact hroot.hOcc 362
  · exact hroot.hOcc 372
  · exact hroot.hOcc 392
  · exact hroot.hOcc 401
  · exact hroot.hOcc 403
  · exact hroot.hOcc 414
  · change (∑ j, (-1 : Int) * x j) ≤ -plane485GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (28 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (21 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (14 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (11 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (39 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (29 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (18 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (26 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (22 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22

end QiushiMatmul
