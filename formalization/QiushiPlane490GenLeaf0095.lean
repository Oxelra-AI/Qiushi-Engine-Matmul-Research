import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0095Refs : Fin 44 → RowRef 713 43 := ![.occ 93, .occ 95, .occ 103, .occ 105, .occ 108, .occ 109, .occ 119, .occ 141, .occ 152, .occ 156, .occ 170, .occ 193, .occ 197, .occ 203, .occ 209, .occ 274, .occ 283, .occ 290, .occ 299, .occ 311, .occ 336, .occ 338, .occ 354, .occ 361, .occ 406, .occ 414, .occ 443, .occ 505, .occ 526, .occ 549, .occ 557, .occ 598, .occ 599, .occ 628, .occ 638, .occ 640, .occ 683, .occ 704, .occ 711, .sumGe, .branchGe 29 (1), .branchLe 18 (0), .branchGe 12 (1), .branchGe 2 (1)]

def plane490GenLeaf0095Mult : Fin 44 → Nat := ![147, 1758, 3095, 6257, 4126, 3944, 5025, 796, 1631, 184, 3162, 1026, 6892, 35, 3624, 797, 70, 163, 626, 648, 4210, 406, 2738, 2253, 6639, 230, 240, 84, 2395, 3148, 49, 322, 84, 84, 98, 2752, 106, 49, 35, 7011, 19069, 7011, 34377, 23535]

theorem plane490GenLeaf0095 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_18 : x 18 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0095Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0095Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0095Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0095Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 93
  · exact hroot.hOcc 95
  · exact hroot.hOcc 103
  · exact hroot.hOcc 105
  · exact hroot.hOcc 108
  · exact hroot.hOcc 109
  · exact hroot.hOcc 119
  · exact hroot.hOcc 141
  · exact hroot.hOcc 152
  · exact hroot.hOcc 156
  · exact hroot.hOcc 170
  · exact hroot.hOcc 193
  · exact hroot.hOcc 197
  · exact hroot.hOcc 203
  · exact hroot.hOcc 209
  · exact hroot.hOcc 274
  · exact hroot.hOcc 283
  · exact hroot.hOcc 290
  · exact hroot.hOcc 299
  · exact hroot.hOcc 311
  · exact hroot.hOcc 336
  · exact hroot.hOcc 338
  · exact hroot.hOcc 354
  · exact hroot.hOcc 361
  · exact hroot.hOcc 406
  · exact hroot.hOcc 414
  · exact hroot.hOcc 443
  · exact hroot.hOcc 505
  · exact hroot.hOcc 526
  · exact hroot.hOcc 549
  · exact hroot.hOcc 557
  · exact hroot.hOcc 598
  · exact hroot.hOcc 599
  · exact hroot.hOcc 628
  · exact hroot.hOcc 638
  · exact hroot.hOcc 640
  · exact hroot.hOcc 683
  · exact hroot.hOcc 704
  · exact hroot.hOcc 711
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (12 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2

end QiushiMatmul
