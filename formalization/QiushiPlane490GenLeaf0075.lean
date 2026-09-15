import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0075Refs : Fin 43 → RowRef 713 43 := ![.occ 90, .occ 102, .occ 104, .occ 119, .occ 128, .occ 151, .occ 196, .occ 235, .occ 239, .occ 242, .occ 249, .occ 252, .occ 257, .occ 274, .occ 291, .occ 295, .occ 297, .occ 314, .occ 343, .occ 408, .occ 431, .occ 456, .occ 466, .occ 479, .occ 483, .occ 484, .occ 493, .occ 501, .occ 542, .occ 630, .occ 655, .occ 656, .occ 657, .occ 667, .occ 673, .occ 679, .sumGe, .nonneg 33, .branchLe 29 (0), .branchGe 4 (1), .branchGe 34 (1), .branchGe 3 (1), .branchGe 1 (1)]

def plane490GenLeaf0075Mult : Fin 43 → Nat := ![496, 1666, 52, 1120, 234, 407, 2128, 144, 483, 92, 284, 201, 62, 90, 615, 462, 143, 111, 270, 127, 825, 744, 575, 180, 761, 263, 180, 180, 90, 194, 1430, 299, 1068, 180, 21, 788, 2308, 675, 698, 8143, 5470, 7805, 5403]

theorem plane490GenLeaf0075 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0075Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0075Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0075Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0075Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 90
  · exact hroot.hOcc 102
  · exact hroot.hOcc 104
  · exact hroot.hOcc 119
  · exact hroot.hOcc 128
  · exact hroot.hOcc 151
  · exact hroot.hOcc 196
  · exact hroot.hOcc 235
  · exact hroot.hOcc 239
  · exact hroot.hOcc 242
  · exact hroot.hOcc 249
  · exact hroot.hOcc 252
  · exact hroot.hOcc 257
  · exact hroot.hOcc 274
  · exact hroot.hOcc 291
  · exact hroot.hOcc 295
  · exact hroot.hOcc 297
  · exact hroot.hOcc 314
  · exact hroot.hOcc 343
  · exact hroot.hOcc 408
  · exact hroot.hOcc 431
  · exact hroot.hOcc 456
  · exact hroot.hOcc 466
  · exact hroot.hOcc 479
  · exact hroot.hOcc 483
  · exact hroot.hOcc 484
  · exact hroot.hOcc 493
  · exact hroot.hOcc 501
  · exact hroot.hOcc 542
  · exact hroot.hOcc 630
  · exact hroot.hOcc 655
  · exact hroot.hOcc 656
  · exact hroot.hOcc 657
  · exact hroot.hOcc 667
  · exact hroot.hOcc 673
  · exact hroot.hOcc 679
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (33 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1

end QiushiMatmul
