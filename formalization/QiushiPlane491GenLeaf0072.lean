import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0072Refs : Fin 49 → RowRef 726 49 := ![.occ 82, .occ 83, .occ 95, .occ 96, .occ 97, .occ 136, .occ 137, .occ 185, .occ 187, .occ 192, .occ 223, .occ 244, .occ 258, .occ 281, .occ 319, .occ 323, .occ 324, .occ 332, .occ 336, .occ 352, .occ 356, .occ 358, .occ 367, .occ 368, .occ 372, .occ 385, .occ 394, .occ 396, .occ 419, .occ 429, .occ 478, .occ 490, .occ 524, .occ 525, .occ 534, .occ 541, .occ 580, .occ 636, .occ 651, .occ 664, .occ 703, .occ 721, .sumGe, .nonneg 2, .nonneg 47, .branchLe 31 (0), .branchGe 16 (1), .branchGe 20 (1), .branchGe 38 (1)]

def plane491GenLeaf0072Mult : Fin 49 → Nat := ![1644, 9607, 4722, 7349, 6553, 29008, 25686, 1582, 7681, 4082, 12381, 1644, 12895, 3114, 30816, 11519, 2191, 15570, 22984, 10585, 17275, 1644, 8931, 1644, 12066, 17139, 16789, 19747, 18273, 35603, 5714, 14697, 16459, 20247, 1644, 670, 5491, 1132, 9042, 14960, 2201, 6037, 60445, 7444, 9628, 48926, 312430, 81287, 128503]

theorem plane491GenLeaf0072 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0072Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0072Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0072Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0072Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 82
  · exact hroot.hOcc 83
  · exact hroot.hOcc 95
  · exact hroot.hOcc 96
  · exact hroot.hOcc 97
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 185
  · exact hroot.hOcc 187
  · exact hroot.hOcc 192
  · exact hroot.hOcc 223
  · exact hroot.hOcc 244
  · exact hroot.hOcc 258
  · exact hroot.hOcc 281
  · exact hroot.hOcc 319
  · exact hroot.hOcc 323
  · exact hroot.hOcc 324
  · exact hroot.hOcc 332
  · exact hroot.hOcc 336
  · exact hroot.hOcc 352
  · exact hroot.hOcc 356
  · exact hroot.hOcc 358
  · exact hroot.hOcc 367
  · exact hroot.hOcc 368
  · exact hroot.hOcc 372
  · exact hroot.hOcc 385
  · exact hroot.hOcc 394
  · exact hroot.hOcc 396
  · exact hroot.hOcc 419
  · exact hroot.hOcc 429
  · exact hroot.hOcc 478
  · exact hroot.hOcc 490
  · exact hroot.hOcc 524
  · exact hroot.hOcc 525
  · exact hroot.hOcc 534
  · exact hroot.hOcc 541
  · exact hroot.hOcc 580
  · exact hroot.hOcc 636
  · exact hroot.hOcc 651
  · exact hroot.hOcc 664
  · exact hroot.hOcc 703
  · exact hroot.hOcc 721
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (47 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (20 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20
  · change (∑ k, (if k = (38 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38

end QiushiMatmul
