import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0054Refs : Fin 50 → RowRef 726 49 := ![.occ 78, .occ 100, .occ 106, .occ 114, .occ 116, .occ 123, .occ 124, .occ 194, .occ 217, .occ 254, .occ 257, .occ 293, .occ 304, .occ 338, .occ 368, .occ 370, .occ 372, .occ 373, .occ 382, .occ 401, .occ 409, .occ 416, .occ 430, .occ 431, .occ 470, .occ 568, .occ 570, .occ 571, .occ 580, .occ 603, .occ 626, .occ 630, .occ 632, .occ 634, .occ 639, .occ 642, .occ 644, .occ 653, .occ 691, .occ 704, .sumGe, .nonneg 24, .branchLe 31 (0), .branchLe 16 (0), .branchGe 27 (1), .branchLe 11 (0), .branchLe 23 (0), .branchLe 0 (0), .branchGe 43 (1), .branchGe 48 (1)]

def plane491GenLeaf0054Mult : Fin 50 → Nat := ![43100, 92545, 135344, 212020, 10053, 21351, 140767, 37953, 106401, 36162, 45329, 21342, 2535, 19569, 35550, 121026, 20940, 54365, 32070, 23634, 48831, 41908, 20507, 97729, 42629, 73499, 56670, 32070, 31901, 23567, 42463, 38366, 6132, 9759, 18640, 21788, 9456, 53931, 37615, 26807, 253849, 28951, 253849, 221948, 387467, 209351, 125231, 192667, 471488, 722951]

theorem plane491GenLeaf0054 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_48 : (1 : Int) ≤ x 48)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_43 : (1 : Int) ≤ x 43)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0054Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0054Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0054Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0054Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 78
  · exact hroot.hOcc 100
  · exact hroot.hOcc 106
  · exact hroot.hOcc 114
  · exact hroot.hOcc 116
  · exact hroot.hOcc 123
  · exact hroot.hOcc 124
  · exact hroot.hOcc 194
  · exact hroot.hOcc 217
  · exact hroot.hOcc 254
  · exact hroot.hOcc 257
  · exact hroot.hOcc 293
  · exact hroot.hOcc 304
  · exact hroot.hOcc 338
  · exact hroot.hOcc 368
  · exact hroot.hOcc 370
  · exact hroot.hOcc 372
  · exact hroot.hOcc 373
  · exact hroot.hOcc 382
  · exact hroot.hOcc 401
  · exact hroot.hOcc 409
  · exact hroot.hOcc 416
  · exact hroot.hOcc 430
  · exact hroot.hOcc 431
  · exact hroot.hOcc 470
  · exact hroot.hOcc 568
  · exact hroot.hOcc 570
  · exact hroot.hOcc 571
  · exact hroot.hOcc 580
  · exact hroot.hOcc 603
  · exact hroot.hOcc 626
  · exact hroot.hOcc 630
  · exact hroot.hOcc 632
  · exact hroot.hOcc 634
  · exact hroot.hOcc 639
  · exact hroot.hOcc 642
  · exact hroot.hOcc 644
  · exact hroot.hOcc 653
  · exact hroot.hOcc 691
  · exact hroot.hOcc 704
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (24 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (11 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (23 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (0 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (43 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_43
  · change (∑ k, (if k = (48 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_48

end QiushiMatmul
