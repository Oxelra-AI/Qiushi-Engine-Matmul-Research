import QiushiPlane485GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane485GenLeaf0015Refs : Fin 42 → RowRef 421 41 := ![.occ 87, .occ 105, .occ 108, .occ 133, .occ 134, .occ 135, .occ 136, .occ 137, .occ 154, .occ 155, .occ 167, .occ 170, .occ 175, .occ 179, .occ 184, .occ 196, .occ 211, .occ 250, .occ 252, .occ 276, .occ 287, .occ 298, .occ 302, .occ 323, .occ 349, .occ 351, .occ 352, .occ 366, .occ 372, .occ 375, .occ 380, .occ 396, .occ 416, .sumGe, .branchLe 28 (0), .branchLe 21 (0), .branchGe 14 (1), .branchLe 29 (0), .branchLe 13 (0), .branchLe 15 (0), .branchLe 31 (0), .branchGe 4 (1)]

def plane485GenLeaf0015Mult : Fin 42 → Nat := ![712, 3874, 1866, 2364, 176, 3136, 3762, 8016, 8049, 656, 419, 1308, 911, 3103, 3620, 6127, 295, 12762, 9196, 486, 2850, 330, 5984, 1934, 5726, 928, 942, 3078, 2126, 2560, 3574, 1798, 520, 17968, 17968, 17118, 51762, 13124, 6046, 12040, 8772, 17704]

theorem plane485GenLeaf0015 (x : Fin 41 → Int)
    (hroot : plane485GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane485GenLeaf0015Refs i).resolveCoeff plane485GenOccSys j)
    (fun i => (plane485GenLeaf0015Refs i).resolveRhs plane485GenOccSys) plane485GenLeaf0015Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane485GenLeaf0015Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 105
  · exact hroot.hOcc 108
  · exact hroot.hOcc 133
  · exact hroot.hOcc 134
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 154
  · exact hroot.hOcc 155
  · exact hroot.hOcc 167
  · exact hroot.hOcc 170
  · exact hroot.hOcc 175
  · exact hroot.hOcc 179
  · exact hroot.hOcc 184
  · exact hroot.hOcc 196
  · exact hroot.hOcc 211
  · exact hroot.hOcc 250
  · exact hroot.hOcc 252
  · exact hroot.hOcc 276
  · exact hroot.hOcc 287
  · exact hroot.hOcc 298
  · exact hroot.hOcc 302
  · exact hroot.hOcc 323
  · exact hroot.hOcc 349
  · exact hroot.hOcc 351
  · exact hroot.hOcc 352
  · exact hroot.hOcc 366
  · exact hroot.hOcc 372
  · exact hroot.hOcc 375
  · exact hroot.hOcc 380
  · exact hroot.hOcc 396
  · exact hroot.hOcc 416
  · change (∑ j, (-1 : Int) * x j) ≤ -plane485GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (28 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (21 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (14 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (29 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (13 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (15 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (31 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (4 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4

end QiushiMatmul
