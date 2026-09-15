import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0061Refs : Fin 44 → RowRef 713 43 := ![.occ 90, .occ 93, .occ 106, .occ 109, .occ 110, .occ 115, .occ 128, .occ 175, .occ 195, .occ 196, .occ 202, .occ 235, .occ 244, .occ 247, .occ 252, .occ 268, .occ 274, .occ 290, .occ 295, .occ 316, .occ 317, .occ 375, .occ 384, .occ 464, .occ 468, .occ 470, .occ 533, .occ 570, .occ 599, .occ 607, .occ 632, .occ 635, .occ 649, .occ 673, .occ 677, .occ 695, .sumGe, .branchLe 29 (0), .branchGe 4 (1), .branchLe 34 (0), .branchLe 23 (0), .branchGe 39 (1), .branchLe 18 (0), .branchGe 15 (1)]

def plane490GenLeaf0061Mult : Fin 44 → Nat := ![28380, 3495, 9391, 12677, 4400, 34261, 58600, 60946, 18372, 27338, 30094, 43734, 33723, 6174, 49523, 12583, 56195, 37997, 27971, 1327, 30595, 34665, 7593, 9997, 3725, 8957, 8113, 28624, 10240, 3735, 23781, 3020, 3291, 29166, 10385, 12860, 110469, 82953, 418751, 44501, 110469, 103183, 102356, 70322]

theorem plane490GenLeaf0061 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0061Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0061Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0061Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0061Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 90
  · exact hroot.hOcc 93
  · exact hroot.hOcc 106
  · exact hroot.hOcc 109
  · exact hroot.hOcc 110
  · exact hroot.hOcc 115
  · exact hroot.hOcc 128
  · exact hroot.hOcc 175
  · exact hroot.hOcc 195
  · exact hroot.hOcc 196
  · exact hroot.hOcc 202
  · exact hroot.hOcc 235
  · exact hroot.hOcc 244
  · exact hroot.hOcc 247
  · exact hroot.hOcc 252
  · exact hroot.hOcc 268
  · exact hroot.hOcc 274
  · exact hroot.hOcc 290
  · exact hroot.hOcc 295
  · exact hroot.hOcc 316
  · exact hroot.hOcc 317
  · exact hroot.hOcc 375
  · exact hroot.hOcc 384
  · exact hroot.hOcc 464
  · exact hroot.hOcc 468
  · exact hroot.hOcc 470
  · exact hroot.hOcc 533
  · exact hroot.hOcc 570
  · exact hroot.hOcc 599
  · exact hroot.hOcc 607
  · exact hroot.hOcc 632
  · exact hroot.hOcc 635
  · exact hroot.hOcc 649
  · exact hroot.hOcc 673
  · exact hroot.hOcc 677
  · exact hroot.hOcc 695
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (39 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15

end QiushiMatmul
