import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0031Refs : Fin 50 → RowRef 726 49 := ![.occ 83, .occ 102, .occ 105, .occ 116, .occ 119, .occ 157, .occ 158, .occ 159, .occ 243, .occ 293, .occ 304, .occ 320, .occ 335, .occ 351, .occ 368, .occ 374, .occ 375, .occ 379, .occ 382, .occ 390, .occ 394, .occ 400, .occ 420, .occ 425, .occ 487, .occ 489, .occ 501, .occ 533, .occ 558, .occ 584, .occ 594, .occ 628, .occ 671, .occ 674, .occ 704, .occ 714, .occ 718, .sumGe, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchGe 29 (1), .branchLe 43 (0), .branchLe 9 (0), .branchLe 5 (0), .branchLe 44 (0), .branchLe 24 (0), .branchLe 4 (0), .branchGe 26 (1), .branchLe 45 (0)]

def plane491GenLeaf0031Mult : Fin 50 → Nat := ![27035, 84503, 34423, 133000, 7741, 10895, 58135, 37386, 9775, 43752, 44982, 5643, 8351, 119, 15544, 44052, 11673, 9223, 10690, 2086, 28553, 15991, 24236, 36640, 22662, 14871, 52172, 54396, 26951, 31827, 4933, 53454, 18500, 5768, 34039, 16905, 24865, 183030, 112358, 114250, 152615, 505113, 101597, 143463, 35314, 106221, 153232, 166125, 72994, 182911]

theorem plane491GenLeaf0031 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_45 : x 45 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_43 : x 43 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0031Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0031Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0031Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0031Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 83
  · exact hroot.hOcc 102
  · exact hroot.hOcc 105
  · exact hroot.hOcc 116
  · exact hroot.hOcc 119
  · exact hroot.hOcc 157
  · exact hroot.hOcc 158
  · exact hroot.hOcc 159
  · exact hroot.hOcc 243
  · exact hroot.hOcc 293
  · exact hroot.hOcc 304
  · exact hroot.hOcc 320
  · exact hroot.hOcc 335
  · exact hroot.hOcc 351
  · exact hroot.hOcc 368
  · exact hroot.hOcc 374
  · exact hroot.hOcc 375
  · exact hroot.hOcc 379
  · exact hroot.hOcc 382
  · exact hroot.hOcc 390
  · exact hroot.hOcc 394
  · exact hroot.hOcc 400
  · exact hroot.hOcc 420
  · exact hroot.hOcc 425
  · exact hroot.hOcc 487
  · exact hroot.hOcc 489
  · exact hroot.hOcc 501
  · exact hroot.hOcc 533
  · exact hroot.hOcc 558
  · exact hroot.hOcc 584
  · exact hroot.hOcc 594
  · exact hroot.hOcc 628
  · exact hroot.hOcc 671
  · exact hroot.hOcc 674
  · exact hroot.hOcc 704
  · exact hroot.hOcc 714
  · exact hroot.hOcc 718
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (43 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (9 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (5 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (44 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (24 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (4 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (26 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (45 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_45

end QiushiMatmul
