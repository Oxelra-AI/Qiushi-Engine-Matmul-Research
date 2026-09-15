import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0063Refs : Fin 50 → RowRef 726 49 := ![.occ 103, .occ 106, .occ 116, .occ 117, .occ 129, .occ 130, .occ 206, .occ 207, .occ 219, .occ 222, .occ 232, .occ 315, .occ 317, .occ 327, .occ 329, .occ 340, .occ 343, .occ 365, .occ 366, .occ 368, .occ 370, .occ 407, .occ 431, .occ 475, .occ 485, .occ 486, .occ 489, .occ 524, .occ 528, .occ 548, .occ 563, .occ 570, .occ 573, .occ 632, .occ 642, .occ 648, .occ 653, .occ 662, .occ 700, .occ 713, .occ 715, .sumGe, .nonneg 32, .nonneg 42, .branchLe 31 (0), .branchLe 16 (0), .branchGe 27 (1), .branchGe 11 (1), .branchLe 44 (0), .branchGe 46 (1)]

def plane491GenLeaf0063Mult : Fin 50 → Nat := ![209608, 230792, 241647, 124788, 18992, 15306, 236971, 47354, 29814, 48316, 32000, 137404, 64250, 22700, 83011, 159911, 163571, 27033, 27323, 24323, 12001, 15674, 77889, 539, 37408, 46387, 71698, 7839, 273, 51023, 41191, 25172, 18112, 2733, 43226, 30368, 47997, 71325, 25712, 27982, 21435, 309471, 69501, 106604, 51044, 273650, 711459, 603115, 281216, 1087493]

theorem plane491GenLeaf0063 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_46 : (1 : Int) ≤ x 46)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0063Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0063Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0063Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0063Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 103
  · exact hroot.hOcc 106
  · exact hroot.hOcc 116
  · exact hroot.hOcc 117
  · exact hroot.hOcc 129
  · exact hroot.hOcc 130
  · exact hroot.hOcc 206
  · exact hroot.hOcc 207
  · exact hroot.hOcc 219
  · exact hroot.hOcc 222
  · exact hroot.hOcc 232
  · exact hroot.hOcc 315
  · exact hroot.hOcc 317
  · exact hroot.hOcc 327
  · exact hroot.hOcc 329
  · exact hroot.hOcc 340
  · exact hroot.hOcc 343
  · exact hroot.hOcc 365
  · exact hroot.hOcc 366
  · exact hroot.hOcc 368
  · exact hroot.hOcc 370
  · exact hroot.hOcc 407
  · exact hroot.hOcc 431
  · exact hroot.hOcc 475
  · exact hroot.hOcc 485
  · exact hroot.hOcc 486
  · exact hroot.hOcc 489
  · exact hroot.hOcc 524
  · exact hroot.hOcc 528
  · exact hroot.hOcc 548
  · exact hroot.hOcc 563
  · exact hroot.hOcc 570
  · exact hroot.hOcc 573
  · exact hroot.hOcc 632
  · exact hroot.hOcc 642
  · exact hroot.hOcc 648
  · exact hroot.hOcc 653
  · exact hroot.hOcc 662
  · exact hroot.hOcc 700
  · exact hroot.hOcc 713
  · exact hroot.hOcc 715
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (32 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (42 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (11 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11
  · change (∑ k, (if k = (44 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (46 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_46

end QiushiMatmul
