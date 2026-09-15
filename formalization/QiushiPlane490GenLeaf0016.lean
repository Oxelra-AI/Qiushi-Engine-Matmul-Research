import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0016Refs : Fin 44 → RowRef 713 43 := ![.occ 85, .occ 86, .occ 89, .occ 94, .occ 95, .occ 102, .occ 103, .occ 110, .occ 111, .occ 150, .occ 157, .occ 205, .occ 220, .occ 247, .occ 260, .occ 268, .occ 309, .occ 314, .occ 335, .occ 364, .occ 440, .occ 477, .occ 484, .occ 494, .occ 501, .occ 518, .occ 540, .occ 552, .occ 599, .occ 604, .occ 641, .occ 662, .occ 666, .occ 692, .occ 697, .occ 710, .sumGe, .branchLe 29 (0), .branchLe 4 (0), .branchLe 23 (0), .branchGe 16 (1), .branchLe 15 (0), .branchLe 21 (0), .branchGe 32 (1)]

def plane490GenLeaf0016Mult : Fin 44 → Nat := ![53, 107, 146, 323, 233, 45, 356, 4, 162, 31, 23, 113, 40, 63, 161, 8, 148, 9, 112, 29, 19, 28, 15, 1, 153, 113, 18, 12, 19, 76, 29, 50, 147, 85, 4, 3, 378, 221, 359, 378, 1012, 378, 341, 788]

theorem plane490GenLeaf0016 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0016Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0016Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0016Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0016Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 85
  · exact hroot.hOcc 86
  · exact hroot.hOcc 89
  · exact hroot.hOcc 94
  · exact hroot.hOcc 95
  · exact hroot.hOcc 102
  · exact hroot.hOcc 103
  · exact hroot.hOcc 110
  · exact hroot.hOcc 111
  · exact hroot.hOcc 150
  · exact hroot.hOcc 157
  · exact hroot.hOcc 205
  · exact hroot.hOcc 220
  · exact hroot.hOcc 247
  · exact hroot.hOcc 260
  · exact hroot.hOcc 268
  · exact hroot.hOcc 309
  · exact hroot.hOcc 314
  · exact hroot.hOcc 335
  · exact hroot.hOcc 364
  · exact hroot.hOcc 440
  · exact hroot.hOcc 477
  · exact hroot.hOcc 484
  · exact hroot.hOcc 494
  · exact hroot.hOcc 501
  · exact hroot.hOcc 518
  · exact hroot.hOcc 540
  · exact hroot.hOcc 552
  · exact hroot.hOcc 599
  · exact hroot.hOcc 604
  · exact hroot.hOcc 641
  · exact hroot.hOcc 662
  · exact hroot.hOcc 666
  · exact hroot.hOcc 692
  · exact hroot.hOcc 697
  · exact hroot.hOcc 710
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (21 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (32 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32

end QiushiMatmul
