import QiushiPlane485GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane485GenLeaf0011Refs : Fin 42 → RowRef 421 41 := ![.occ 87, .occ 90, .occ 135, .occ 136, .occ 137, .occ 141, .occ 155, .occ 163, .occ 167, .occ 170, .occ 173, .occ 182, .occ 184, .occ 210, .occ 213, .occ 225, .occ 226, .occ 228, .occ 232, .occ 239, .occ 249, .occ 257, .occ 276, .occ 279, .occ 304, .occ 313, .occ 319, .occ 328, .occ 333, .occ 335, .occ 344, .occ 376, .occ 398, .occ 400, .occ 401, .sumGe, .branchLe 28 (0), .branchLe 21 (0), .branchLe 14 (0), .branchGe 11 (1), .branchLe 40 (0), .branchLe 13 (0)]

def plane485GenLeaf0011Mult : Fin 42 → Nat := ![393347, 477296, 774013, 378137, 539623, 6014, 141304, 560507, 210778, 89537, 393680, 49590, 51408, 180112, 447502, 21560, 98257, 453722, 258782, 35213, 197075, 229739, 395635, 6220, 51767, 195514, 23582, 85721, 25017, 13455, 165368, 180708, 275977, 176877, 51767, 1386808, 1174863, 917264, 1139886, 1573015, 1207985, 1197912]

theorem plane485GenLeaf0011 (x : Fin 41 → Int)
    (hroot : plane485GenOccSys.RootHolds x)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hUB_40 : x 40 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane485GenLeaf0011Refs i).resolveCoeff plane485GenOccSys j)
    (fun i => (plane485GenLeaf0011Refs i).resolveRhs plane485GenOccSys) plane485GenLeaf0011Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane485GenLeaf0011Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 90
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 141
  · exact hroot.hOcc 155
  · exact hroot.hOcc 163
  · exact hroot.hOcc 167
  · exact hroot.hOcc 170
  · exact hroot.hOcc 173
  · exact hroot.hOcc 182
  · exact hroot.hOcc 184
  · exact hroot.hOcc 210
  · exact hroot.hOcc 213
  · exact hroot.hOcc 225
  · exact hroot.hOcc 226
  · exact hroot.hOcc 228
  · exact hroot.hOcc 232
  · exact hroot.hOcc 239
  · exact hroot.hOcc 249
  · exact hroot.hOcc 257
  · exact hroot.hOcc 276
  · exact hroot.hOcc 279
  · exact hroot.hOcc 304
  · exact hroot.hOcc 313
  · exact hroot.hOcc 319
  · exact hroot.hOcc 328
  · exact hroot.hOcc 333
  · exact hroot.hOcc 335
  · exact hroot.hOcc 344
  · exact hroot.hOcc 376
  · exact hroot.hOcc 398
  · exact hroot.hOcc 400
  · exact hroot.hOcc 401
  · change (∑ j, (-1 : Int) * x j) ≤ -plane485GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (28 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (21 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (14 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (11 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11
  · change (∑ k, (if k = (40 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (13 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13

end QiushiMatmul
