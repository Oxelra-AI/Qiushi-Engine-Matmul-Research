import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0013Refs : Fin 41 → RowRef 713 43 := ![.occ 85, .occ 99, .occ 117, .occ 129, .occ 142, .occ 185, .occ 203, .occ 204, .occ 229, .occ 238, .occ 252, .occ 263, .occ 277, .occ 284, .occ 354, .occ 362, .occ 371, .occ 375, .occ 390, .occ 412, .occ 489, .occ 490, .occ 500, .occ 522, .occ 613, .occ 645, .occ 682, .occ 690, .occ 695, .occ 696, .occ 699, .occ 703, .occ 704, .sumGe, .branchLe 29 (0), .branchLe 4 (0), .branchLe 23 (0), .branchLe 16 (0), .branchGe 39 (1), .branchGe 17 (1), .branchLe 8 (0)]

def plane490GenLeaf0013Mult : Fin 41 → Nat := ![7425, 5911, 1858, 4797, 4491, 6393, 11049, 14505, 578, 1943, 3983, 334, 8569, 9134, 12909, 2468, 3412, 4815, 9726, 2023, 189, 4023, 5485, 6569, 556, 1750, 651, 6339, 4729, 278, 278, 2894, 3023, 26761, 20144, 6393, 26761, 14797, 14638, 86269, 23738]

theorem plane490GenLeaf0013 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0013Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0013Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0013Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0013Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 85
  · exact hroot.hOcc 99
  · exact hroot.hOcc 117
  · exact hroot.hOcc 129
  · exact hroot.hOcc 142
  · exact hroot.hOcc 185
  · exact hroot.hOcc 203
  · exact hroot.hOcc 204
  · exact hroot.hOcc 229
  · exact hroot.hOcc 238
  · exact hroot.hOcc 252
  · exact hroot.hOcc 263
  · exact hroot.hOcc 277
  · exact hroot.hOcc 284
  · exact hroot.hOcc 354
  · exact hroot.hOcc 362
  · exact hroot.hOcc 371
  · exact hroot.hOcc 375
  · exact hroot.hOcc 390
  · exact hroot.hOcc 412
  · exact hroot.hOcc 489
  · exact hroot.hOcc 490
  · exact hroot.hOcc 500
  · exact hroot.hOcc 522
  · exact hroot.hOcc 613
  · exact hroot.hOcc 645
  · exact hroot.hOcc 682
  · exact hroot.hOcc 690
  · exact hroot.hOcc 695
  · exact hroot.hOcc 696
  · exact hroot.hOcc 699
  · exact hroot.hOcc 703
  · exact hroot.hOcc 704
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (39 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8

end QiushiMatmul
