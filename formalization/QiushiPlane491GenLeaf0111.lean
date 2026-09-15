import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0111Refs : Fin 50 → RowRef 726 49 := ![.occ 82, .occ 98, .occ 112, .occ 113, .occ 118, .occ 151, .occ 175, .occ 178, .occ 197, .occ 198, .occ 231, .occ 237, .occ 248, .occ 275, .occ 319, .occ 332, .occ 350, .occ 359, .occ 364, .occ 377, .occ 393, .occ 404, .occ 413, .occ 431, .occ 495, .occ 523, .occ 528, .occ 534, .occ 568, .occ 580, .occ 603, .occ 606, .occ 607, .occ 611, .occ 626, .occ 627, .occ 632, .occ 640, .occ 651, .occ 691, .occ 723, .sumGe, .nonneg 19, .branchGe 31 (1), .branchGe 44 (1), .branchGe 6 (1), .branchLe 15 (0), .branchLe 9 (0), .branchGe 14 (1), .branchLe 22 (0)]

def plane491GenLeaf0111Mult : Fin 50 → Nat := ![177467, 211239, 240841, 57367, 260756, 89621, 18219, 90450, 20734, 40939, 2942, 12300, 16380, 54699, 25695, 59154, 4165, 38530, 75074, 17240, 44365, 142924, 11962, 1288, 99830, 24199, 33663, 10564, 12432, 50151, 9405, 26885, 101459, 71126, 23320, 7911, 24272, 123477, 79342, 81530, 23480, 299286, 82369, 820409, 863141, 225209, 175809, 202382, 595378, 297998]

theorem plane491GenLeaf0111 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_44 : (1 : Int) ≤ x 44)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0111Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0111Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0111Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0111Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 82
  · exact hroot.hOcc 98
  · exact hroot.hOcc 112
  · exact hroot.hOcc 113
  · exact hroot.hOcc 118
  · exact hroot.hOcc 151
  · exact hroot.hOcc 175
  · exact hroot.hOcc 178
  · exact hroot.hOcc 197
  · exact hroot.hOcc 198
  · exact hroot.hOcc 231
  · exact hroot.hOcc 237
  · exact hroot.hOcc 248
  · exact hroot.hOcc 275
  · exact hroot.hOcc 319
  · exact hroot.hOcc 332
  · exact hroot.hOcc 350
  · exact hroot.hOcc 359
  · exact hroot.hOcc 364
  · exact hroot.hOcc 377
  · exact hroot.hOcc 393
  · exact hroot.hOcc 404
  · exact hroot.hOcc 413
  · exact hroot.hOcc 431
  · exact hroot.hOcc 495
  · exact hroot.hOcc 523
  · exact hroot.hOcc 528
  · exact hroot.hOcc 534
  · exact hroot.hOcc 568
  · exact hroot.hOcc 580
  · exact hroot.hOcc 603
  · exact hroot.hOcc 606
  · exact hroot.hOcc 607
  · exact hroot.hOcc 611
  · exact hroot.hOcc 626
  · exact hroot.hOcc 627
  · exact hroot.hOcc 632
  · exact hroot.hOcc 640
  · exact hroot.hOcc 651
  · exact hroot.hOcc 691
  · exact hroot.hOcc 723
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (19 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_44
  · change (∑ k, (if k = (6 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (15 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (9 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (14 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (22 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22

end QiushiMatmul
