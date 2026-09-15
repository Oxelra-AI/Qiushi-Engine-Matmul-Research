import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0074Refs : Fin 44 → RowRef 713 43 := ![.occ 89, .occ 90, .occ 102, .occ 104, .occ 106, .occ 109, .occ 114, .occ 115, .occ 117, .occ 130, .occ 133, .occ 156, .occ 158, .occ 177, .occ 202, .occ 204, .occ 239, .occ 265, .occ 274, .occ 291, .occ 297, .occ 314, .occ 335, .occ 343, .occ 349, .occ 350, .occ 362, .occ 427, .occ 431, .occ 479, .occ 486, .occ 542, .occ 553, .occ 572, .occ 630, .occ 667, .occ 679, .occ 683, .sumGe, .branchLe 29 (0), .branchGe 4 (1), .branchGe 34 (1), .branchGe 3 (1), .branchLe 1 (0)]

def plane490GenLeaf0074Mult : Fin 44 → Nat := ![585, 660, 389, 107, 117, 53, 29, 113, 325, 25, 250, 21, 428, 165, 2, 332, 27, 179, 422, 223, 38, 48, 9, 354, 37, 334, 77, 72, 187, 217, 54, 55, 16, 73, 126, 30, 107, 183, 660, 424, 1384, 1867, 2179, 660]

theorem plane490GenLeaf0074 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0074Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0074Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0074Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0074Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 89
  · exact hroot.hOcc 90
  · exact hroot.hOcc 102
  · exact hroot.hOcc 104
  · exact hroot.hOcc 106
  · exact hroot.hOcc 109
  · exact hroot.hOcc 114
  · exact hroot.hOcc 115
  · exact hroot.hOcc 117
  · exact hroot.hOcc 130
  · exact hroot.hOcc 133
  · exact hroot.hOcc 156
  · exact hroot.hOcc 158
  · exact hroot.hOcc 177
  · exact hroot.hOcc 202
  · exact hroot.hOcc 204
  · exact hroot.hOcc 239
  · exact hroot.hOcc 265
  · exact hroot.hOcc 274
  · exact hroot.hOcc 291
  · exact hroot.hOcc 297
  · exact hroot.hOcc 314
  · exact hroot.hOcc 335
  · exact hroot.hOcc 343
  · exact hroot.hOcc 349
  · exact hroot.hOcc 350
  · exact hroot.hOcc 362
  · exact hroot.hOcc 427
  · exact hroot.hOcc 431
  · exact hroot.hOcc 479
  · exact hroot.hOcc 486
  · exact hroot.hOcc 542
  · exact hroot.hOcc 553
  · exact hroot.hOcc 572
  · exact hroot.hOcc 630
  · exact hroot.hOcc 667
  · exact hroot.hOcc 679
  · exact hroot.hOcc 683
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1

end QiushiMatmul
