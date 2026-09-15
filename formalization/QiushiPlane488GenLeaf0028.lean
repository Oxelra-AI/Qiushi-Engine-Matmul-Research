import QiushiPlane488GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane488GenLeaf0028Refs : Fin 42 → RowRef 413 41 := ![.occ 94, .occ 98, .occ 100, .occ 105, .occ 148, .occ 156, .occ 160, .occ 162, .occ 175, .occ 190, .occ 195, .occ 196, .occ 203, .occ 205, .occ 210, .occ 224, .occ 225, .occ 226, .occ 231, .occ 232, .occ 262, .occ 266, .occ 273, .occ 293, .occ 300, .occ 317, .occ 331, .occ 332, .occ 334, .occ 342, .occ 344, .occ 349, .occ 355, .occ 357, .occ 360, .occ 380, .sumGe, .nonneg 7, .branchGe 27 (1), .branchLe 19 (0), .branchGe 16 (1), .branchLe 39 (0)]

def plane488GenLeaf0028Mult : Fin 42 → Nat := ![2746, 28485, 751, 12927, 352, 29872, 2885, 2731, 49996, 7152, 20723, 13294, 12690, 14925, 27758, 15995, 10410, 4245, 37063, 20723, 6526, 2116, 9229, 6745, 33228, 6392, 2664, 1272, 6760, 3103, 7825, 6138, 30093, 26446, 1633, 18247, 84232, 71890, 176175, 11789, 123908, 81129]

theorem plane488GenLeaf0028 (x : Fin 41 → Int)
    (hroot : plane488GenOccSys.RootHolds x)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane488GenLeaf0028Refs i).resolveCoeff plane488GenOccSys j)
    (fun i => (plane488GenLeaf0028Refs i).resolveRhs plane488GenOccSys) plane488GenLeaf0028Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane488GenLeaf0028Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 94
  · exact hroot.hOcc 98
  · exact hroot.hOcc 100
  · exact hroot.hOcc 105
  · exact hroot.hOcc 148
  · exact hroot.hOcc 156
  · exact hroot.hOcc 160
  · exact hroot.hOcc 162
  · exact hroot.hOcc 175
  · exact hroot.hOcc 190
  · exact hroot.hOcc 195
  · exact hroot.hOcc 196
  · exact hroot.hOcc 203
  · exact hroot.hOcc 205
  · exact hroot.hOcc 210
  · exact hroot.hOcc 224
  · exact hroot.hOcc 225
  · exact hroot.hOcc 226
  · exact hroot.hOcc 231
  · exact hroot.hOcc 232
  · exact hroot.hOcc 262
  · exact hroot.hOcc 266
  · exact hroot.hOcc 273
  · exact hroot.hOcc 293
  · exact hroot.hOcc 300
  · exact hroot.hOcc 317
  · exact hroot.hOcc 331
  · exact hroot.hOcc 332
  · exact hroot.hOcc 334
  · exact hroot.hOcc 342
  · exact hroot.hOcc 344
  · exact hroot.hOcc 349
  · exact hroot.hOcc 355
  · exact hroot.hOcc 357
  · exact hroot.hOcc 360
  · exact hroot.hOcc 380
  · change (∑ j, (-1 : Int) * x j) ≤ -plane488GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (27 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (19 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (16 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (39 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39

end QiushiMatmul
