import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0059Refs : Fin 43 → RowRef 713 43 := ![.occ 91, .occ 104, .occ 111, .occ 115, .occ 116, .occ 119, .occ 128, .occ 175, .occ 193, .occ 202, .occ 204, .occ 217, .occ 244, .occ 249, .occ 252, .occ 268, .occ 274, .occ 291, .occ 295, .occ 314, .occ 335, .occ 362, .occ 364, .occ 447, .occ 448, .occ 456, .occ 466, .occ 494, .occ 532, .occ 533, .occ 578, .occ 657, .occ 662, .occ 696, .occ 706, .occ 708, .sumGe, .nonneg 10, .branchLe 29 (0), .branchGe 4 (1), .branchLe 34 (0), .branchLe 23 (0), .branchLe 39 (0)]

def plane490GenLeaf0059Mult : Fin 43 → Nat := ![3804, 7353, 671, 13825, 12888, 8537, 7662, 1345, 2659, 9330, 9553, 4475, 12651, 4794, 6974, 4478, 14713, 2676, 13691, 3499, 4945, 4248, 1747, 1141, 8302, 7793, 5678, 225, 2724, 5391, 1156, 991, 916, 4569, 1429, 4138, 31621, 2191, 27052, 103552, 8585, 30192, 31621]

theorem plane490GenLeaf0059 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0059Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0059Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0059Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0059Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 91
  · exact hroot.hOcc 104
  · exact hroot.hOcc 111
  · exact hroot.hOcc 115
  · exact hroot.hOcc 116
  · exact hroot.hOcc 119
  · exact hroot.hOcc 128
  · exact hroot.hOcc 175
  · exact hroot.hOcc 193
  · exact hroot.hOcc 202
  · exact hroot.hOcc 204
  · exact hroot.hOcc 217
  · exact hroot.hOcc 244
  · exact hroot.hOcc 249
  · exact hroot.hOcc 252
  · exact hroot.hOcc 268
  · exact hroot.hOcc 274
  · exact hroot.hOcc 291
  · exact hroot.hOcc 295
  · exact hroot.hOcc 314
  · exact hroot.hOcc 335
  · exact hroot.hOcc 362
  · exact hroot.hOcc 364
  · exact hroot.hOcc 447
  · exact hroot.hOcc 448
  · exact hroot.hOcc 456
  · exact hroot.hOcc 466
  · exact hroot.hOcc 494
  · exact hroot.hOcc 532
  · exact hroot.hOcc 533
  · exact hroot.hOcc 578
  · exact hroot.hOcc 657
  · exact hroot.hOcc 662
  · exact hroot.hOcc 696
  · exact hroot.hOcc 706
  · exact hroot.hOcc 708
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39

end QiushiMatmul
