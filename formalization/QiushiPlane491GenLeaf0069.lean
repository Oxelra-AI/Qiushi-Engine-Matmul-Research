import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0069Refs : Fin 50 → RowRef 726 49 := ![.occ 83, .occ 89, .occ 95, .occ 96, .occ 100, .occ 106, .occ 115, .occ 135, .occ 223, .occ 227, .occ 231, .occ 248, .occ 284, .occ 298, .occ 299, .occ 318, .occ 326, .occ 331, .occ 355, .occ 358, .occ 365, .occ 367, .occ 372, .occ 380, .occ 385, .occ 392, .occ 400, .occ 419, .occ 429, .occ 490, .occ 506, .occ 510, .occ 524, .occ 529, .occ 588, .occ 603, .occ 605, .occ 609, .occ 648, .occ 669, .occ 691, .occ 703, .occ 714, .sumGe, .nonneg 8, .nonneg 40, .branchLe 31 (0), .branchGe 16 (1), .branchLe 20 (0), .branchGe 27 (1)]

def plane491GenLeaf0069Mult : Fin 50 → Nat := ![47183, 14499, 266555, 259630, 98546, 185378, 60693, 244722, 12277, 41747, 69668, 8776, 32287, 4956, 157580, 19104, 9620, 95765, 13960, 5985, 116012, 15827, 11600, 16364, 167123, 23743, 69170, 125646, 103735, 69770, 5550, 40199, 76384, 130854, 65543, 11572, 42740, 33937, 17758, 3667, 15838, 27314, 3667, 328800, 13670, 599, 293415, 1614888, 301486, 617609]

theorem plane491GenLeaf0069 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0069Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0069Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0069Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0069Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 83
  · exact hroot.hOcc 89
  · exact hroot.hOcc 95
  · exact hroot.hOcc 96
  · exact hroot.hOcc 100
  · exact hroot.hOcc 106
  · exact hroot.hOcc 115
  · exact hroot.hOcc 135
  · exact hroot.hOcc 223
  · exact hroot.hOcc 227
  · exact hroot.hOcc 231
  · exact hroot.hOcc 248
  · exact hroot.hOcc 284
  · exact hroot.hOcc 298
  · exact hroot.hOcc 299
  · exact hroot.hOcc 318
  · exact hroot.hOcc 326
  · exact hroot.hOcc 331
  · exact hroot.hOcc 355
  · exact hroot.hOcc 358
  · exact hroot.hOcc 365
  · exact hroot.hOcc 367
  · exact hroot.hOcc 372
  · exact hroot.hOcc 380
  · exact hroot.hOcc 385
  · exact hroot.hOcc 392
  · exact hroot.hOcc 400
  · exact hroot.hOcc 419
  · exact hroot.hOcc 429
  · exact hroot.hOcc 490
  · exact hroot.hOcc 506
  · exact hroot.hOcc 510
  · exact hroot.hOcc 524
  · exact hroot.hOcc 529
  · exact hroot.hOcc 588
  · exact hroot.hOcc 603
  · exact hroot.hOcc 605
  · exact hroot.hOcc 609
  · exact hroot.hOcc 648
  · exact hroot.hOcc 669
  · exact hroot.hOcc 691
  · exact hroot.hOcc 703
  · exact hroot.hOcc 714
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (40 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (20 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (27 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27

end QiushiMatmul
