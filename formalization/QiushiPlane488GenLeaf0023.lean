import QiushiPlane488GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane488GenLeaf0023Refs : Fin 42 → RowRef 413 41 := ![.occ 86, .occ 91, .occ 92, .occ 96, .occ 97, .occ 102, .occ 105, .occ 136, .occ 140, .occ 164, .occ 165, .occ 175, .occ 178, .occ 183, .occ 189, .occ 190, .occ 195, .occ 196, .occ 226, .occ 231, .occ 234, .occ 241, .occ 254, .occ 255, .occ 293, .occ 300, .occ 303, .occ 310, .occ 317, .occ 324, .occ 360, .occ 375, .occ 395, .occ 410, .sumGe, .nonneg 7, .nonneg 13, .branchGe 27 (1), .branchLe 19 (0), .branchLe 16 (0), .branchLe 22 (0), .branchLe 40 (0)]

def plane488GenLeaf0023Mult : Fin 42 → Nat := ![254, 662, 1053, 1137, 710, 540, 3259, 832, 595, 79, 154, 2756, 902, 430, 1168, 7, 221, 1703, 1212, 1540, 22, 46, 702, 1620, 1324, 2034, 1154, 1211, 57, 508, 410, 777, 487, 614, 4634, 485, 422, 17390, 4634, 1389, 3094, 3123]

theorem plane488GenLeaf0023 (x : Fin 41 → Int)
    (hroot : plane488GenOccSys.RootHolds x)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hUB_40 : x 40 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane488GenLeaf0023Refs i).resolveCoeff plane488GenOccSys j)
    (fun i => (plane488GenLeaf0023Refs i).resolveRhs plane488GenOccSys) plane488GenLeaf0023Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane488GenLeaf0023Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 86
  · exact hroot.hOcc 91
  · exact hroot.hOcc 92
  · exact hroot.hOcc 96
  · exact hroot.hOcc 97
  · exact hroot.hOcc 102
  · exact hroot.hOcc 105
  · exact hroot.hOcc 136
  · exact hroot.hOcc 140
  · exact hroot.hOcc 164
  · exact hroot.hOcc 165
  · exact hroot.hOcc 175
  · exact hroot.hOcc 178
  · exact hroot.hOcc 183
  · exact hroot.hOcc 189
  · exact hroot.hOcc 190
  · exact hroot.hOcc 195
  · exact hroot.hOcc 196
  · exact hroot.hOcc 226
  · exact hroot.hOcc 231
  · exact hroot.hOcc 234
  · exact hroot.hOcc 241
  · exact hroot.hOcc 254
  · exact hroot.hOcc 255
  · exact hroot.hOcc 293
  · exact hroot.hOcc 300
  · exact hroot.hOcc 303
  · exact hroot.hOcc 310
  · exact hroot.hOcc 317
  · exact hroot.hOcc 324
  · exact hroot.hOcc 360
  · exact hroot.hOcc 375
  · exact hroot.hOcc 395
  · exact hroot.hOcc 410
  · change (∑ j, (-1 : Int) * x j) ≤ -plane488GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (13 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (27 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (19 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (16 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (22 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (40 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40

end QiushiMatmul
