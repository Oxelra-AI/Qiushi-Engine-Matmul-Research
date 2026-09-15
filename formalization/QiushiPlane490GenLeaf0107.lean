import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0107Refs : Fin 44 → RowRef 713 43 := ![.occ 93, .occ 99, .occ 104, .occ 106, .occ 108, .occ 111, .occ 119, .occ 120, .occ 146, .occ 159, .occ 178, .occ 197, .occ 208, .occ 237, .occ 246, .occ 248, .occ 250, .occ 297, .occ 299, .occ 354, .occ 362, .occ 395, .occ 446, .occ 479, .occ 480, .occ 500, .occ 508, .occ 509, .occ 538, .occ 550, .occ 587, .occ 602, .occ 608, .occ 609, .occ 671, .occ 706, .sumGe, .branchGe 29 (1), .branchGe 18 (1), .branchLe 14 (0), .branchGe 1 (1), .branchGe 20 (1), .branchLe 8 (0), .branchGe 2 (1)]

def plane490GenLeaf0107Mult : Fin 44 → Nat := ![1291, 60, 538, 850, 377, 74, 53, 729, 371, 400, 156, 192, 555, 336, 697, 170, 30, 31, 482, 370, 358, 336, 315, 141, 6, 30, 253, 87, 127, 214, 179, 591, 248, 447, 229, 253, 1297, 3258, 2338, 1083, 1346, 3515, 1297, 2919]

theorem plane490GenLeaf0107 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0107Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0107Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0107Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0107Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 93
  · exact hroot.hOcc 99
  · exact hroot.hOcc 104
  · exact hroot.hOcc 106
  · exact hroot.hOcc 108
  · exact hroot.hOcc 111
  · exact hroot.hOcc 119
  · exact hroot.hOcc 120
  · exact hroot.hOcc 146
  · exact hroot.hOcc 159
  · exact hroot.hOcc 178
  · exact hroot.hOcc 197
  · exact hroot.hOcc 208
  · exact hroot.hOcc 237
  · exact hroot.hOcc 246
  · exact hroot.hOcc 248
  · exact hroot.hOcc 250
  · exact hroot.hOcc 297
  · exact hroot.hOcc 299
  · exact hroot.hOcc 354
  · exact hroot.hOcc 362
  · exact hroot.hOcc 395
  · exact hroot.hOcc 446
  · exact hroot.hOcc 479
  · exact hroot.hOcc 480
  · exact hroot.hOcc 500
  · exact hroot.hOcc 508
  · exact hroot.hOcc 509
  · exact hroot.hOcc 538
  · exact hroot.hOcc 550
  · exact hroot.hOcc 587
  · exact hroot.hOcc 602
  · exact hroot.hOcc 608
  · exact hroot.hOcc 609
  · exact hroot.hOcc 671
  · exact hroot.hOcc 706
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2

end QiushiMatmul
