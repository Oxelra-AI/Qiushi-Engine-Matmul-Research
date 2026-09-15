import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0109Refs : Fin 50 → RowRef 726 49 := ![.occ 98, .occ 112, .occ 116, .occ 171, .occ 175, .occ 195, .occ 198, .occ 200, .occ 255, .occ 258, .occ 267, .occ 275, .occ 318, .occ 323, .occ 332, .occ 335, .occ 340, .occ 350, .occ 377, .occ 393, .occ 410, .occ 415, .occ 423, .occ 425, .occ 451, .occ 495, .occ 509, .occ 528, .occ 568, .occ 586, .occ 587, .occ 606, .occ 607, .occ 611, .occ 632, .occ 651, .occ 652, .occ 673, .occ 692, .occ 713, .occ 722, .sumGe, .nonneg 33, .branchGe 31 (1), .branchGe 44 (1), .branchGe 6 (1), .branchLe 15 (0), .branchLe 9 (0), .branchLe 14 (0), .branchLe 36 (0)]

def plane491GenLeaf0109Mult : Fin 50 → Nat := ![132469, 138864, 44432, 43790, 42042, 17316, 10236, 41189, 116587, 3357, 36335, 67881, 40384, 24750, 533, 24676, 28275, 41016, 3134, 15134, 44785, 750, 10664, 6541, 25492, 34648, 53958, 18016, 9663, 27934, 38636, 17431, 42174, 34825, 8556, 71495, 23689, 12730, 19437, 31597, 3357, 195562, 34086, 335520, 633641, 429349, 167628, 128584, 192205, 105848]

theorem plane491GenLeaf0109 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_44 : (1 : Int) ≤ x 44)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_36 : x 36 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0109Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0109Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0109Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0109Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 98
  · exact hroot.hOcc 112
  · exact hroot.hOcc 116
  · exact hroot.hOcc 171
  · exact hroot.hOcc 175
  · exact hroot.hOcc 195
  · exact hroot.hOcc 198
  · exact hroot.hOcc 200
  · exact hroot.hOcc 255
  · exact hroot.hOcc 258
  · exact hroot.hOcc 267
  · exact hroot.hOcc 275
  · exact hroot.hOcc 318
  · exact hroot.hOcc 323
  · exact hroot.hOcc 332
  · exact hroot.hOcc 335
  · exact hroot.hOcc 340
  · exact hroot.hOcc 350
  · exact hroot.hOcc 377
  · exact hroot.hOcc 393
  · exact hroot.hOcc 410
  · exact hroot.hOcc 415
  · exact hroot.hOcc 423
  · exact hroot.hOcc 425
  · exact hroot.hOcc 451
  · exact hroot.hOcc 495
  · exact hroot.hOcc 509
  · exact hroot.hOcc 528
  · exact hroot.hOcc 568
  · exact hroot.hOcc 586
  · exact hroot.hOcc 587
  · exact hroot.hOcc 606
  · exact hroot.hOcc 607
  · exact hroot.hOcc 611
  · exact hroot.hOcc 632
  · exact hroot.hOcc 651
  · exact hroot.hOcc 652
  · exact hroot.hOcc 673
  · exact hroot.hOcc 692
  · exact hroot.hOcc 713
  · exact hroot.hOcc 722
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (33 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_44
  · change (∑ k, (if k = (6 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (15 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (9 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (14 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (36 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36

end QiushiMatmul
