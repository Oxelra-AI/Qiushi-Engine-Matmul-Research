import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0032Refs : Fin 50 → RowRef 726 49 := ![.occ 115, .occ 120, .occ 219, .occ 229, .occ 282, .occ 283, .occ 301, .occ 304, .occ 324, .occ 358, .occ 364, .occ 382, .occ 393, .occ 400, .occ 409, .occ 420, .occ 425, .occ 489, .occ 501, .occ 506, .occ 508, .occ 511, .occ 532, .occ 533, .occ 542, .occ 558, .occ 559, .occ 581, .occ 628, .occ 642, .occ 654, .occ 685, .occ 702, .occ 704, .occ 713, .occ 718, .occ 725, .sumGe, .nonneg 48, .branchLe 31 (0), .branchLe 27 (0), .branchGe 29 (1), .branchLe 43 (0), .branchLe 9 (0), .branchLe 5 (0), .branchLe 44 (0), .branchLe 24 (0), .branchLe 4 (0), .branchGe 26 (1), .branchGe 45 (1)]

def plane491GenLeaf0032Mult : Fin 50 → Nat := ![877342, 71916, 209479, 19070, 63891, 312399, 229818, 212518, 678413, 47283, 1582862, 117396, 472434, 696544, 590270, 187761, 618802, 110034, 310245, 366796, 553677, 182521, 159056, 326319, 422344, 115158, 306270, 184984, 618117, 490825, 430818, 204204, 61121, 265734, 571387, 450428, 105603, 2767916, 1333448, 1879634, 1027470, 4807748, 1953968, 2391713, 879065, 887892, 700892, 2010035, 1754882, 5011832]

theorem plane491GenLeaf0032 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_45 : (1 : Int) ≤ x 45)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_43 : x 43 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0032Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0032Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0032Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0032Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 115
  · exact hroot.hOcc 120
  · exact hroot.hOcc 219
  · exact hroot.hOcc 229
  · exact hroot.hOcc 282
  · exact hroot.hOcc 283
  · exact hroot.hOcc 301
  · exact hroot.hOcc 304
  · exact hroot.hOcc 324
  · exact hroot.hOcc 358
  · exact hroot.hOcc 364
  · exact hroot.hOcc 382
  · exact hroot.hOcc 393
  · exact hroot.hOcc 400
  · exact hroot.hOcc 409
  · exact hroot.hOcc 420
  · exact hroot.hOcc 425
  · exact hroot.hOcc 489
  · exact hroot.hOcc 501
  · exact hroot.hOcc 506
  · exact hroot.hOcc 508
  · exact hroot.hOcc 511
  · exact hroot.hOcc 532
  · exact hroot.hOcc 533
  · exact hroot.hOcc 542
  · exact hroot.hOcc 558
  · exact hroot.hOcc 559
  · exact hroot.hOcc 581
  · exact hroot.hOcc 628
  · exact hroot.hOcc 642
  · exact hroot.hOcc 654
  · exact hroot.hOcc 685
  · exact hroot.hOcc 702
  · exact hroot.hOcc 704
  · exact hroot.hOcc 713
  · exact hroot.hOcc 718
  · exact hroot.hOcc 725
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (48 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (43 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (9 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (5 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (44 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (24 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (4 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (26 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (45 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_45

end QiushiMatmul
