import QiushiPlane485GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane485GenLeaf0000Refs : Fin 42 → RowRef 421 41 := ![.occ 87, .occ 112, .occ 116, .occ 136, .occ 141, .occ 144, .occ 145, .occ 155, .occ 161, .occ 162, .occ 163, .occ 164, .occ 167, .occ 182, .occ 210, .occ 213, .occ 232, .occ 246, .occ 253, .occ 257, .occ 262, .occ 265, .occ 276, .occ 279, .occ 284, .occ 287, .occ 297, .occ 298, .occ 300, .occ 302, .occ 337, .occ 359, .occ 403, .occ 406, .sumGe, .branchLe 28 (0), .branchLe 21 (0), .branchLe 14 (0), .branchLe 11 (0), .branchLe 39 (0), .branchLe 17 (0), .branchLe 10 (0)]

def plane485GenLeaf0000Mult : Fin 42 → Nat := ![495706, 27394, 145752, 582991, 51105, 375537, 50245, 12258, 111110, 5006, 210832, 402626, 153768, 359522, 124696, 270708, 18744, 257198, 228458, 418862, 167080, 113198, 161218, 25950, 313506, 428166, 125590, 98510, 353230, 185890, 119400, 74502, 292540, 276932, 1471818, 940478, 1118016, 1285928, 560790, 1397316, 702060, 1471818]

theorem plane485GenLeaf0000 (x : Fin 41 → Int)
    (hroot : plane485GenOccSys.RootHolds x)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane485GenLeaf0000Refs i).resolveCoeff plane485GenOccSys j)
    (fun i => (plane485GenLeaf0000Refs i).resolveRhs plane485GenOccSys) plane485GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane485GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 112
  · exact hroot.hOcc 116
  · exact hroot.hOcc 136
  · exact hroot.hOcc 141
  · exact hroot.hOcc 144
  · exact hroot.hOcc 145
  · exact hroot.hOcc 155
  · exact hroot.hOcc 161
  · exact hroot.hOcc 162
  · exact hroot.hOcc 163
  · exact hroot.hOcc 164
  · exact hroot.hOcc 167
  · exact hroot.hOcc 182
  · exact hroot.hOcc 210
  · exact hroot.hOcc 213
  · exact hroot.hOcc 232
  · exact hroot.hOcc 246
  · exact hroot.hOcc 253
  · exact hroot.hOcc 257
  · exact hroot.hOcc 262
  · exact hroot.hOcc 265
  · exact hroot.hOcc 276
  · exact hroot.hOcc 279
  · exact hroot.hOcc 284
  · exact hroot.hOcc 287
  · exact hroot.hOcc 297
  · exact hroot.hOcc 298
  · exact hroot.hOcc 300
  · exact hroot.hOcc 302
  · exact hroot.hOcc 337
  · exact hroot.hOcc 359
  · exact hroot.hOcc 403
  · exact hroot.hOcc 406
  · change (∑ j, (-1 : Int) * x j) ≤ -plane485GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (28 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (21 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (14 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (11 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (39 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (17 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (10 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10

end QiushiMatmul
