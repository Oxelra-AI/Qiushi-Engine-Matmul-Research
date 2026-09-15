import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0087Refs : Fin 50 → RowRef 726 49 := ![.occ 84, .occ 91, .occ 96, .occ 98, .occ 100, .occ 102, .occ 110, .occ 114, .occ 121, .occ 231, .occ 323, .occ 350, .occ 368, .occ 401, .occ 410, .occ 416, .occ 429, .occ 431, .occ 484, .occ 490, .occ 499, .occ 508, .occ 524, .occ 526, .occ 529, .occ 548, .occ 601, .occ 606, .occ 610, .occ 611, .occ 622, .occ 658, .occ 662, .occ 685, .occ 708, .occ 720, .occ 722, .sumGe, .nonneg 13, .nonneg 30, .nonneg 33, .nonneg 37, .nonneg 41, .branchGe 31 (1), .branchLe 44 (0), .branchLe 11 (0), .branchGe 27 (1), .branchGe 43 (1), .branchLe 42 (0), .branchGe 38 (1)]

def plane491GenLeaf0087Mult : Fin 50 → Nat := ![8302, 1460, 52427, 94579, 134331, 26305, 30914, 112477, 98912, 9554, 212675, 89175, 67730, 1174, 62430, 77068, 41521, 3953, 12615, 52540, 71418, 33179, 10212, 34580, 33815, 74709, 16914, 29681, 15083, 10246, 35746, 25027, 10336, 10432, 31714, 14974, 28511, 222229, 5420, 24016, 108546, 52272, 181889, 521117, 193718, 183382, 637327, 249532, 147000, 499196]

theorem plane491GenLeaf0087 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hLB_43 : (1 : Int) ≤ x 43)
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0087Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0087Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0087Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0087Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 84
  · exact hroot.hOcc 91
  · exact hroot.hOcc 96
  · exact hroot.hOcc 98
  · exact hroot.hOcc 100
  · exact hroot.hOcc 102
  · exact hroot.hOcc 110
  · exact hroot.hOcc 114
  · exact hroot.hOcc 121
  · exact hroot.hOcc 231
  · exact hroot.hOcc 323
  · exact hroot.hOcc 350
  · exact hroot.hOcc 368
  · exact hroot.hOcc 401
  · exact hroot.hOcc 410
  · exact hroot.hOcc 416
  · exact hroot.hOcc 429
  · exact hroot.hOcc 431
  · exact hroot.hOcc 484
  · exact hroot.hOcc 490
  · exact hroot.hOcc 499
  · exact hroot.hOcc 508
  · exact hroot.hOcc 524
  · exact hroot.hOcc 526
  · exact hroot.hOcc 529
  · exact hroot.hOcc 548
  · exact hroot.hOcc 601
  · exact hroot.hOcc 606
  · exact hroot.hOcc 610
  · exact hroot.hOcc 611
  · exact hroot.hOcc 622
  · exact hroot.hOcc 658
  · exact hroot.hOcc 662
  · exact hroot.hOcc 685
  · exact hroot.hOcc 708
  · exact hroot.hOcc 720
  · exact hroot.hOcc 722
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (13 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (30 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (33 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (37 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (41 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (11 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (27 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (43 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_43
  · change (∑ k, (if k = (42 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (38 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38

end QiushiMatmul
