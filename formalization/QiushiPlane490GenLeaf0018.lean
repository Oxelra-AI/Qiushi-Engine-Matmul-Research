import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0018Refs : Fin 44 → RowRef 713 43 := ![.occ 87, .occ 91, .occ 92, .occ 94, .occ 95, .occ 99, .occ 100, .occ 102, .occ 116, .occ 121, .occ 127, .occ 201, .occ 205, .occ 236, .occ 238, .occ 271, .occ 291, .occ 303, .occ 352, .occ 353, .occ 362, .occ 364, .occ 375, .occ 444, .occ 445, .occ 489, .occ 521, .occ 522, .occ 599, .occ 601, .occ 665, .occ 672, .occ 704, .occ 710, .sumGe, .branchLe 29 (0), .branchLe 4 (0), .branchLe 23 (0), .branchGe 16 (1), .branchLe 32 (0), .branchLe 3 (0), .branchLe 42 (0), .branchLe 20 (0), .branchLe 38 (0)]

def plane490GenLeaf0018Mult : Fin 44 → Nat := ![174, 271, 424, 775, 539, 457, 50, 215, 205, 110, 488, 382, 302, 44, 537, 79, 223, 100, 93, 196, 159, 125, 157, 191, 360, 117, 149, 180, 340, 42, 199, 130, 143, 228, 1199, 920, 846, 1157, 2552, 1099, 828, 875, 1199, 1199]

theorem plane490GenLeaf0018 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0018Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0018Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0018Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0018Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 91
  · exact hroot.hOcc 92
  · exact hroot.hOcc 94
  · exact hroot.hOcc 95
  · exact hroot.hOcc 99
  · exact hroot.hOcc 100
  · exact hroot.hOcc 102
  · exact hroot.hOcc 116
  · exact hroot.hOcc 121
  · exact hroot.hOcc 127
  · exact hroot.hOcc 201
  · exact hroot.hOcc 205
  · exact hroot.hOcc 236
  · exact hroot.hOcc 238
  · exact hroot.hOcc 271
  · exact hroot.hOcc 291
  · exact hroot.hOcc 303
  · exact hroot.hOcc 352
  · exact hroot.hOcc 353
  · exact hroot.hOcc 362
  · exact hroot.hOcc 364
  · exact hroot.hOcc 375
  · exact hroot.hOcc 444
  · exact hroot.hOcc 445
  · exact hroot.hOcc 489
  · exact hroot.hOcc 521
  · exact hroot.hOcc 522
  · exact hroot.hOcc 599
  · exact hroot.hOcc 601
  · exact hroot.hOcc 665
  · exact hroot.hOcc 672
  · exact hroot.hOcc 704
  · exact hroot.hOcc 710
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (38 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38

end QiushiMatmul
