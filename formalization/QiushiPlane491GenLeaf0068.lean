import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0068Refs : Fin 49 → RowRef 726 49 := ![.occ 80, .occ 89, .occ 95, .occ 96, .occ 109, .occ 129, .occ 131, .occ 135, .occ 223, .occ 230, .occ 240, .occ 257, .occ 278, .occ 287, .occ 293, .occ 298, .occ 299, .occ 318, .occ 331, .occ 332, .occ 334, .occ 366, .occ 367, .occ 371, .occ 372, .occ 377, .occ 385, .occ 400, .occ 419, .occ 429, .occ 478, .occ 490, .occ 570, .occ 578, .occ 585, .occ 595, .occ 599, .occ 650, .occ 664, .occ 691, .occ 702, .occ 721, .sumGe, .nonneg 2, .branchLe 31 (0), .branchGe 16 (1), .branchLe 20 (0), .branchLe 27 (0), .branchGe 9 (1)]

def plane491GenLeaf0068Mult : Fin 49 → Nat := ![2862, 2033, 3581, 8807, 4355, 7657, 1432, 14288, 16474, 3052, 4795, 3599, 1814, 93, 917, 5469, 4568, 2594, 4296, 6941, 7607, 1578, 1876, 1934, 1620, 1662, 3991, 11802, 5409, 10319, 5708, 3073, 1620, 2728, 413, 4614, 9276, 4171, 2118, 413, 4259, 649, 24868, 4977, 17261, 118930, 13474, 18722, 53081]

theorem plane491GenLeaf0068 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0068Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0068Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0068Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0068Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 80
  · exact hroot.hOcc 89
  · exact hroot.hOcc 95
  · exact hroot.hOcc 96
  · exact hroot.hOcc 109
  · exact hroot.hOcc 129
  · exact hroot.hOcc 131
  · exact hroot.hOcc 135
  · exact hroot.hOcc 223
  · exact hroot.hOcc 230
  · exact hroot.hOcc 240
  · exact hroot.hOcc 257
  · exact hroot.hOcc 278
  · exact hroot.hOcc 287
  · exact hroot.hOcc 293
  · exact hroot.hOcc 298
  · exact hroot.hOcc 299
  · exact hroot.hOcc 318
  · exact hroot.hOcc 331
  · exact hroot.hOcc 332
  · exact hroot.hOcc 334
  · exact hroot.hOcc 366
  · exact hroot.hOcc 367
  · exact hroot.hOcc 371
  · exact hroot.hOcc 372
  · exact hroot.hOcc 377
  · exact hroot.hOcc 385
  · exact hroot.hOcc 400
  · exact hroot.hOcc 419
  · exact hroot.hOcc 429
  · exact hroot.hOcc 478
  · exact hroot.hOcc 490
  · exact hroot.hOcc 570
  · exact hroot.hOcc 578
  · exact hroot.hOcc 585
  · exact hroot.hOcc 595
  · exact hroot.hOcc 599
  · exact hroot.hOcc 650
  · exact hroot.hOcc 664
  · exact hroot.hOcc 691
  · exact hroot.hOcc 702
  · exact hroot.hOcc 721
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (20 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (9 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9

end QiushiMatmul
