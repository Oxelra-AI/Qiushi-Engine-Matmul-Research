import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0072Refs : Fin 44 → RowRef 713 43 := ![.occ 94, .occ 100, .occ 102, .occ 104, .occ 106, .occ 126, .occ 128, .occ 154, .occ 155, .occ 192, .occ 196, .occ 201, .occ 204, .occ 229, .occ 237, .occ 238, .occ 252, .occ 274, .occ 283, .occ 290, .occ 291, .occ 322, .occ 335, .occ 350, .occ 364, .occ 376, .occ 388, .occ 448, .occ 493, .occ 560, .occ 572, .occ 638, .occ 655, .occ 673, .occ 685, .occ 711, .sumGe, .nonneg 41, .branchLe 29 (0), .branchGe 4 (1), .branchGe 34 (1), .branchLe 3 (0), .branchLe 40 (0), .branchGe 14 (1)]

def plane490GenLeaf0072Mult : Fin 44 → Nat := ![32, 2392, 1260, 1333, 529, 2057, 743, 123, 612, 811, 227, 1125, 2145, 576, 85, 1365, 780, 1488, 988, 3119, 483, 312, 156, 929, 727, 158, 688, 388, 242, 156, 1457, 881, 662, 344, 71, 639, 3758, 1471, 3096, 8874, 5433, 2869, 2789, 11959]

theorem plane490GenLeaf0072 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hUB_40 : x 40 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0072Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0072Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0072Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0072Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 94
  · exact hroot.hOcc 100
  · exact hroot.hOcc 102
  · exact hroot.hOcc 104
  · exact hroot.hOcc 106
  · exact hroot.hOcc 126
  · exact hroot.hOcc 128
  · exact hroot.hOcc 154
  · exact hroot.hOcc 155
  · exact hroot.hOcc 192
  · exact hroot.hOcc 196
  · exact hroot.hOcc 201
  · exact hroot.hOcc 204
  · exact hroot.hOcc 229
  · exact hroot.hOcc 237
  · exact hroot.hOcc 238
  · exact hroot.hOcc 252
  · exact hroot.hOcc 274
  · exact hroot.hOcc 283
  · exact hroot.hOcc 290
  · exact hroot.hOcc 291
  · exact hroot.hOcc 322
  · exact hroot.hOcc 335
  · exact hroot.hOcc 350
  · exact hroot.hOcc 364
  · exact hroot.hOcc 376
  · exact hroot.hOcc 388
  · exact hroot.hOcc 448
  · exact hroot.hOcc 493
  · exact hroot.hOcc 560
  · exact hroot.hOcc 572
  · exact hroot.hOcc 638
  · exact hroot.hOcc 655
  · exact hroot.hOcc 673
  · exact hroot.hOcc 685
  · exact hroot.hOcc 711
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (41 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (40 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14

end QiushiMatmul
