import QiushiPlane488GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane488GenLeaf0009Refs : Fin 42 → RowRef 413 41 := ![.occ 86, .occ 98, .occ 112, .occ 129, .occ 140, .occ 153, .occ 158, .occ 159, .occ 173, .occ 174, .occ 189, .occ 190, .occ 195, .occ 204, .occ 210, .occ 211, .occ 212, .occ 216, .occ 219, .occ 225, .occ 226, .occ 232, .occ 245, .occ 256, .occ 261, .occ 265, .occ 287, .occ 309, .occ 349, .occ 369, .occ 381, .occ 386, .occ 401, .sumGe, .nonneg 7, .branchLe 27 (0), .branchLe 15 (0), .branchLe 20 (0), .branchGe 25 (1), .branchLe 1 (0), .branchLe 6 (0), .branchGe 3 (1)]

def plane488GenLeaf0009Mult : Fin 42 → Nat := ![56, 615, 483, 562, 534, 88, 89, 621, 339, 473, 218, 392, 672, 92, 4, 516, 307, 416, 193, 195, 13, 515, 176, 81, 78, 430, 47, 107, 261, 254, 35, 138, 107, 1268, 93, 390, 857, 280, 2513, 1179, 417, 2267]

theorem plane488GenLeaf0009 (x : Fin 41 → Int)
    (hroot : plane488GenOccSys.RootHolds x)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane488GenLeaf0009Refs i).resolveCoeff plane488GenOccSys j)
    (fun i => (plane488GenLeaf0009Refs i).resolveRhs plane488GenOccSys) plane488GenLeaf0009Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane488GenLeaf0009Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 86
  · exact hroot.hOcc 98
  · exact hroot.hOcc 112
  · exact hroot.hOcc 129
  · exact hroot.hOcc 140
  · exact hroot.hOcc 153
  · exact hroot.hOcc 158
  · exact hroot.hOcc 159
  · exact hroot.hOcc 173
  · exact hroot.hOcc 174
  · exact hroot.hOcc 189
  · exact hroot.hOcc 190
  · exact hroot.hOcc 195
  · exact hroot.hOcc 204
  · exact hroot.hOcc 210
  · exact hroot.hOcc 211
  · exact hroot.hOcc 212
  · exact hroot.hOcc 216
  · exact hroot.hOcc 219
  · exact hroot.hOcc 225
  · exact hroot.hOcc 226
  · exact hroot.hOcc 232
  · exact hroot.hOcc 245
  · exact hroot.hOcc 256
  · exact hroot.hOcc 261
  · exact hroot.hOcc 265
  · exact hroot.hOcc 287
  · exact hroot.hOcc 309
  · exact hroot.hOcc 349
  · exact hroot.hOcc 369
  · exact hroot.hOcc 381
  · exact hroot.hOcc 386
  · exact hroot.hOcc 401
  · change (∑ j, (-1 : Int) * x j) ≤ -plane488GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (27 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (15 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (20 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (25 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25
  · change (∑ k, (if k = (1 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (6 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (3 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3

end QiushiMatmul
