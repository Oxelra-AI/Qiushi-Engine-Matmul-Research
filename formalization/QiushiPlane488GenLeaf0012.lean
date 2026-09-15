import QiushiPlane488GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane488GenLeaf0012Refs : Fin 35 → RowRef 413 41 := ![.occ 88, .occ 91, .occ 100, .occ 112, .occ 129, .occ 132, .occ 140, .occ 156, .occ 158, .occ 160, .occ 170, .occ 174, .occ 203, .occ 212, .occ 215, .occ 225, .occ 232, .occ 241, .occ 244, .occ 262, .occ 265, .occ 312, .occ 334, .occ 349, .occ 378, .sumGe, .nonneg 7, .nonneg 20, .nonneg 26, .branchLe 27 (0), .branchLe 15 (0), .branchGe 25 (1), .branchGe 1 (1), .branchLe 6 (0), .branchGe 16 (1)]

def plane488GenLeaf0012Mult : Fin 35 → Nat := ![8, 2, 1, 2, 1, 2, 2, 5, 3, 4, 4, 2, 2, 6, 3, 1, 2, 3, 1, 2, 2, 1, 2, 5, 4, 9, 5, 1, 1, 9, 2, 20, 12, 7, 30]

theorem plane488GenLeaf0012 (x : Fin 41 → Int)
    (hroot : plane488GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane488GenLeaf0012Refs i).resolveCoeff plane488GenOccSys j)
    (fun i => (plane488GenLeaf0012Refs i).resolveRhs plane488GenOccSys) plane488GenLeaf0012Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane488GenLeaf0012Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 88
  · exact hroot.hOcc 91
  · exact hroot.hOcc 100
  · exact hroot.hOcc 112
  · exact hroot.hOcc 129
  · exact hroot.hOcc 132
  · exact hroot.hOcc 140
  · exact hroot.hOcc 156
  · exact hroot.hOcc 158
  · exact hroot.hOcc 160
  · exact hroot.hOcc 170
  · exact hroot.hOcc 174
  · exact hroot.hOcc 203
  · exact hroot.hOcc 212
  · exact hroot.hOcc 215
  · exact hroot.hOcc 225
  · exact hroot.hOcc 232
  · exact hroot.hOcc 241
  · exact hroot.hOcc 244
  · exact hroot.hOcc 262
  · exact hroot.hOcc 265
  · exact hroot.hOcc 312
  · exact hroot.hOcc 334
  · exact hroot.hOcc 349
  · exact hroot.hOcc 378
  · change (∑ j, (-1 : Int) * x j) ≤ -plane488GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (20 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (26 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (27 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (15 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (25 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25
  · change (∑ k, (if k = (1 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (6 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (16 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16

end QiushiMatmul
