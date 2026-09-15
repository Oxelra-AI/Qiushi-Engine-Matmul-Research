import QiushiPlane488GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane488GenLeaf0011Refs : Fin 41 → RowRef 413 41 := ![.occ 91, .occ 100, .occ 112, .occ 129, .occ 132, .occ 140, .occ 157, .occ 158, .occ 163, .occ 171, .occ 177, .occ 187, .occ 195, .occ 211, .occ 216, .occ 219, .occ 225, .occ 241, .occ 244, .occ 248, .occ 275, .occ 305, .occ 308, .occ 311, .occ 323, .occ 349, .occ 359, .occ 360, .occ 363, .occ 381, .occ 408, .occ 411, .sumGe, .nonneg 8, .branchLe 27 (0), .branchLe 15 (0), .branchLe 20 (0), .branchGe 25 (1), .branchGe 1 (1), .branchLe 6 (0), .branchLe 16 (0)]

def plane488GenLeaf0011Mult : Fin 41 → Nat := ![248, 312, 386, 202, 153, 865, 112, 606, 112, 2216, 1766, 168, 90, 282, 625, 839, 196, 696, 949, 113, 2082, 84, 84, 33, 844, 56, 992, 1091, 723, 787, 993, 337, 3199, 10, 186, 2247, 1033, 11759, 7527, 3199, 2537]

theorem plane488GenLeaf0011 (x : Fin 41 → Int)
    (hroot : plane488GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane488GenLeaf0011Refs i).resolveCoeff plane488GenOccSys j)
    (fun i => (plane488GenLeaf0011Refs i).resolveRhs plane488GenOccSys) plane488GenLeaf0011Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane488GenLeaf0011Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 91
  · exact hroot.hOcc 100
  · exact hroot.hOcc 112
  · exact hroot.hOcc 129
  · exact hroot.hOcc 132
  · exact hroot.hOcc 140
  · exact hroot.hOcc 157
  · exact hroot.hOcc 158
  · exact hroot.hOcc 163
  · exact hroot.hOcc 171
  · exact hroot.hOcc 177
  · exact hroot.hOcc 187
  · exact hroot.hOcc 195
  · exact hroot.hOcc 211
  · exact hroot.hOcc 216
  · exact hroot.hOcc 219
  · exact hroot.hOcc 225
  · exact hroot.hOcc 241
  · exact hroot.hOcc 244
  · exact hroot.hOcc 248
  · exact hroot.hOcc 275
  · exact hroot.hOcc 305
  · exact hroot.hOcc 308
  · exact hroot.hOcc 311
  · exact hroot.hOcc 323
  · exact hroot.hOcc 349
  · exact hroot.hOcc 359
  · exact hroot.hOcc 360
  · exact hroot.hOcc 363
  · exact hroot.hOcc 381
  · exact hroot.hOcc 408
  · exact hroot.hOcc 411
  · change (∑ j, (-1 : Int) * x j) ≤ -plane488GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (27 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (15 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (20 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (25 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25
  · change (∑ k, (if k = (1 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (6 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (16 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16

end QiushiMatmul
