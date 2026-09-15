import QiushiPlane485GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane485GenLeaf0007Refs : Fin 42 → RowRef 421 41 := ![.occ 87, .occ 119, .occ 123, .occ 129, .occ 136, .occ 155, .occ 160, .occ 161, .occ 168, .occ 174, .occ 175, .occ 176, .occ 184, .occ 189, .occ 200, .occ 218, .occ 220, .occ 223, .occ 228, .occ 233, .occ 239, .occ 276, .occ 298, .occ 300, .occ 304, .occ 316, .occ 337, .occ 352, .occ 358, .occ 359, .occ 361, .occ 370, .occ 392, .sumGe, .nonneg 7, .branchLe 28 (0), .branchLe 21 (0), .branchLe 14 (0), .branchLe 11 (0), .branchGe 39 (1), .branchLe 29 (0), .branchGe 18 (1)]

def plane485GenLeaf0007Mult : Fin 42 → Nat := ![5080, 1932, 2253, 1077, 1485, 2979, 65, 118, 1754, 642, 3760, 1356, 1765, 746, 9, 2721, 3421, 125, 2824, 336, 2228, 193, 1810, 920, 1541, 1645, 2488, 715, 1171, 631, 1427, 59, 306, 7874, 34, 2866, 3673, 6109, 6389, 10250, 6425, 20361]

theorem plane485GenLeaf0007 (x : Fin 41 → Int)
    (hroot : plane485GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane485GenLeaf0007Refs i).resolveCoeff plane485GenOccSys j)
    (fun i => (plane485GenLeaf0007Refs i).resolveRhs plane485GenOccSys) plane485GenLeaf0007Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane485GenLeaf0007Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 119
  · exact hroot.hOcc 123
  · exact hroot.hOcc 129
  · exact hroot.hOcc 136
  · exact hroot.hOcc 155
  · exact hroot.hOcc 160
  · exact hroot.hOcc 161
  · exact hroot.hOcc 168
  · exact hroot.hOcc 174
  · exact hroot.hOcc 175
  · exact hroot.hOcc 176
  · exact hroot.hOcc 184
  · exact hroot.hOcc 189
  · exact hroot.hOcc 200
  · exact hroot.hOcc 218
  · exact hroot.hOcc 220
  · exact hroot.hOcc 223
  · exact hroot.hOcc 228
  · exact hroot.hOcc 233
  · exact hroot.hOcc 239
  · exact hroot.hOcc 276
  · exact hroot.hOcc 298
  · exact hroot.hOcc 300
  · exact hroot.hOcc 304
  · exact hroot.hOcc 316
  · exact hroot.hOcc 337
  · exact hroot.hOcc 352
  · exact hroot.hOcc 358
  · exact hroot.hOcc 359
  · exact hroot.hOcc 361
  · exact hroot.hOcc 370
  · exact hroot.hOcc 392
  · change (∑ j, (-1 : Int) * x j) ≤ -plane485GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (28 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (21 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (14 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (11 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (39 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (29 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (18 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18

end QiushiMatmul
