import QiushiPlane488GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane488GenLeaf0007Refs : Fin 42 → RowRef 413 41 := ![.occ 111, .occ 118, .occ 126, .occ 153, .occ 154, .occ 156, .occ 175, .occ 176, .occ 183, .occ 187, .occ 189, .occ 190, .occ 212, .occ 214, .occ 216, .occ 225, .occ 244, .occ 252, .occ 259, .occ 272, .occ 276, .occ 278, .occ 309, .occ 327, .occ 339, .occ 345, .occ 362, .occ 364, .occ 368, .occ 383, .occ 386, .occ 401, .occ 402, .occ 406, .sumGe, .nonneg 7, .nonneg 21, .branchLe 27 (0), .branchLe 15 (0), .branchLe 20 (0), .branchLe 25 (0), .branchGe 13 (1)]

def plane488GenLeaf0007Mult : Fin 42 → Nat := ![6313, 9058, 493, 2554, 537, 448, 14095, 1588, 11142, 5979, 7225, 3209, 4341, 1621, 5719, 2250, 4023, 13917, 2062, 6723, 3093, 1291, 1291, 2295, 3683, 2038, 7083, 959, 11080, 6997, 4285, 1446, 3829, 916, 28182, 20890, 2018, 14087, 9367, 28182, 28182, 89713]

theorem plane488GenLeaf0007 (x : Fin 41 → Int)
    (hroot : plane488GenOccSys.RootHolds x)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane488GenLeaf0007Refs i).resolveCoeff plane488GenOccSys j)
    (fun i => (plane488GenLeaf0007Refs i).resolveRhs plane488GenOccSys) plane488GenLeaf0007Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane488GenLeaf0007Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 111
  · exact hroot.hOcc 118
  · exact hroot.hOcc 126
  · exact hroot.hOcc 153
  · exact hroot.hOcc 154
  · exact hroot.hOcc 156
  · exact hroot.hOcc 175
  · exact hroot.hOcc 176
  · exact hroot.hOcc 183
  · exact hroot.hOcc 187
  · exact hroot.hOcc 189
  · exact hroot.hOcc 190
  · exact hroot.hOcc 212
  · exact hroot.hOcc 214
  · exact hroot.hOcc 216
  · exact hroot.hOcc 225
  · exact hroot.hOcc 244
  · exact hroot.hOcc 252
  · exact hroot.hOcc 259
  · exact hroot.hOcc 272
  · exact hroot.hOcc 276
  · exact hroot.hOcc 278
  · exact hroot.hOcc 309
  · exact hroot.hOcc 327
  · exact hroot.hOcc 339
  · exact hroot.hOcc 345
  · exact hroot.hOcc 362
  · exact hroot.hOcc 364
  · exact hroot.hOcc 368
  · exact hroot.hOcc 383
  · exact hroot.hOcc 386
  · exact hroot.hOcc 401
  · exact hroot.hOcc 402
  · exact hroot.hOcc 406
  · change (∑ j, (-1 : Int) * x j) ≤ -plane488GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (21 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (27 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (15 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (20 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (25 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (13 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13

end QiushiMatmul
