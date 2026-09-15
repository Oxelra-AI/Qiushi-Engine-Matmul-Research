import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0109Refs : Fin 44 → RowRef 713 43 := ![.occ 102, .occ 105, .occ 106, .occ 108, .occ 114, .occ 136, .occ 141, .occ 146, .occ 159, .occ 160, .occ 197, .occ 250, .occ 257, .occ 258, .occ 263, .occ 272, .occ 291, .occ 325, .occ 335, .occ 447, .occ 480, .occ 494, .occ 512, .occ 517, .occ 533, .occ 550, .occ 562, .occ 587, .occ 590, .occ 602, .occ 632, .occ 651, .occ 679, .occ 697, .occ 706, .sumGe, .branchGe 29 (1), .branchGe 18 (1), .branchLe 14 (0), .branchGe 1 (1), .branchGe 20 (1), .branchGe 8 (1), .branchGe 0 (1), .branchLe 16 (0)]

def plane490GenLeaf0109Mult : Fin 44 → Nat := ![183, 195, 328, 11, 21, 150, 38, 300, 227, 99, 19, 162, 10, 47, 47, 36, 20, 30, 98, 40, 11, 28, 99, 101, 78, 63, 75, 34, 101, 45, 131, 57, 49, 7, 29, 328, 1079, 821, 79, 45, 880, 797, 67, 226]

theorem plane490GenLeaf0109 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0109Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0109Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0109Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0109Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 102
  · exact hroot.hOcc 105
  · exact hroot.hOcc 106
  · exact hroot.hOcc 108
  · exact hroot.hOcc 114
  · exact hroot.hOcc 136
  · exact hroot.hOcc 141
  · exact hroot.hOcc 146
  · exact hroot.hOcc 159
  · exact hroot.hOcc 160
  · exact hroot.hOcc 197
  · exact hroot.hOcc 250
  · exact hroot.hOcc 257
  · exact hroot.hOcc 258
  · exact hroot.hOcc 263
  · exact hroot.hOcc 272
  · exact hroot.hOcc 291
  · exact hroot.hOcc 325
  · exact hroot.hOcc 335
  · exact hroot.hOcc 447
  · exact hroot.hOcc 480
  · exact hroot.hOcc 494
  · exact hroot.hOcc 512
  · exact hroot.hOcc 517
  · exact hroot.hOcc 533
  · exact hroot.hOcc 550
  · exact hroot.hOcc 562
  · exact hroot.hOcc 587
  · exact hroot.hOcc 590
  · exact hroot.hOcc 602
  · exact hroot.hOcc 632
  · exact hroot.hOcc 651
  · exact hroot.hOcc 679
  · exact hroot.hOcc 697
  · exact hroot.hOcc 706
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16

end QiushiMatmul
