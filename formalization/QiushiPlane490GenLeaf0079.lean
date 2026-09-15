import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0079Refs : Fin 44 → RowRef 713 43 := ![.occ 93, .occ 101, .occ 105, .occ 108, .occ 117, .occ 123, .occ 140, .occ 152, .occ 161, .occ 163, .occ 165, .occ 171, .occ 195, .occ 225, .occ 229, .occ 284, .occ 290, .occ 294, .occ 298, .occ 302, .occ 322, .occ 327, .occ 342, .occ 350, .occ 364, .occ 375, .occ 429, .occ 488, .occ 518, .occ 549, .occ 559, .occ 595, .occ 602, .occ 632, .occ 636, .occ 671, .occ 683, .occ 710, .sumGe, .branchGe 29 (1), .branchLe 18 (0), .branchLe 12 (0), .branchLe 1 (0), .branchGe 10 (1)]

def plane490GenLeaf0079Mult : Fin 44 → Nat := ![26, 324, 2213, 2627, 1275, 1390, 1190, 995, 326, 598, 141, 770, 654, 583, 351, 285, 78, 935, 1611, 188, 924, 482, 166, 235, 772, 418, 780, 12, 765, 193, 105, 209, 374, 830, 297, 209, 414, 162, 2627, 10436, 2253, 1858, 2627, 9510]

theorem plane490GenLeaf0079 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0079Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0079Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0079Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0079Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 93
  · exact hroot.hOcc 101
  · exact hroot.hOcc 105
  · exact hroot.hOcc 108
  · exact hroot.hOcc 117
  · exact hroot.hOcc 123
  · exact hroot.hOcc 140
  · exact hroot.hOcc 152
  · exact hroot.hOcc 161
  · exact hroot.hOcc 163
  · exact hroot.hOcc 165
  · exact hroot.hOcc 171
  · exact hroot.hOcc 195
  · exact hroot.hOcc 225
  · exact hroot.hOcc 229
  · exact hroot.hOcc 284
  · exact hroot.hOcc 290
  · exact hroot.hOcc 294
  · exact hroot.hOcc 298
  · exact hroot.hOcc 302
  · exact hroot.hOcc 322
  · exact hroot.hOcc 327
  · exact hroot.hOcc 342
  · exact hroot.hOcc 350
  · exact hroot.hOcc 364
  · exact hroot.hOcc 375
  · exact hroot.hOcc 429
  · exact hroot.hOcc 488
  · exact hroot.hOcc 518
  · exact hroot.hOcc 549
  · exact hroot.hOcc 559
  · exact hroot.hOcc 595
  · exact hroot.hOcc 602
  · exact hroot.hOcc 632
  · exact hroot.hOcc 636
  · exact hroot.hOcc 671
  · exact hroot.hOcc 683
  · exact hroot.hOcc 710
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (12 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10

end QiushiMatmul
