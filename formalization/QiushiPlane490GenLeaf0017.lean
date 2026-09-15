import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0017Refs : Fin 44 → RowRef 713 43 := ![.occ 89, .occ 94, .occ 95, .occ 99, .occ 111, .occ 113, .occ 114, .occ 116, .occ 127, .occ 165, .occ 201, .occ 236, .occ 237, .occ 249, .occ 271, .occ 284, .occ 291, .occ 300, .occ 303, .occ 335, .occ 352, .occ 364, .occ 372, .occ 375, .occ 378, .occ 397, .occ 441, .occ 492, .occ 494, .occ 500, .occ 536, .occ 649, .occ 666, .occ 675, .occ 692, .occ 697, .sumGe, .nonneg 33, .branchLe 29 (0), .branchLe 4 (0), .branchLe 23 (0), .branchGe 16 (1), .branchLe 15 (0), .branchGe 21 (1)]

def plane490GenLeaf0017Mult : Fin 44 → Nat := ![476, 10569, 14025, 6098, 7086, 10, 17907, 650, 6050, 3070, 7458, 5259, 4182, 2167, 11101, 442, 3420, 1703, 959, 825, 7869, 2157, 3811, 1851, 2435, 7744, 6343, 6338, 3606, 6660, 8105, 3047, 2292, 2200, 4274, 136, 21769, 4511, 21633, 18213, 21769, 86676, 17763, 56822]

theorem plane490GenLeaf0017 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0017Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0017Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0017Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0017Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 89
  · exact hroot.hOcc 94
  · exact hroot.hOcc 95
  · exact hroot.hOcc 99
  · exact hroot.hOcc 111
  · exact hroot.hOcc 113
  · exact hroot.hOcc 114
  · exact hroot.hOcc 116
  · exact hroot.hOcc 127
  · exact hroot.hOcc 165
  · exact hroot.hOcc 201
  · exact hroot.hOcc 236
  · exact hroot.hOcc 237
  · exact hroot.hOcc 249
  · exact hroot.hOcc 271
  · exact hroot.hOcc 284
  · exact hroot.hOcc 291
  · exact hroot.hOcc 300
  · exact hroot.hOcc 303
  · exact hroot.hOcc 335
  · exact hroot.hOcc 352
  · exact hroot.hOcc 364
  · exact hroot.hOcc 372
  · exact hroot.hOcc 375
  · exact hroot.hOcc 378
  · exact hroot.hOcc 397
  · exact hroot.hOcc 441
  · exact hroot.hOcc 492
  · exact hroot.hOcc 494
  · exact hroot.hOcc 500
  · exact hroot.hOcc 536
  · exact hroot.hOcc 649
  · exact hroot.hOcc 666
  · exact hroot.hOcc 675
  · exact hroot.hOcc 692
  · exact hroot.hOcc 697
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (33 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21

end QiushiMatmul
