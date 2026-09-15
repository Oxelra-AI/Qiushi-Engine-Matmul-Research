import QiushiPlane467GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane467GenLeaf0003Refs : Fin 60 → RowRef 84 59 := ![.occ 4, .occ 5, .occ 7, .occ 8, .occ 9, .occ 10, .occ 11, .occ 13, .occ 16, .occ 17, .occ 18, .occ 21, .occ 23, .occ 24, .occ 29, .occ 32, .occ 34, .occ 37, .occ 38, .occ 41, .occ 42, .occ 43, .occ 45, .occ 46, .occ 47, .occ 48, .occ 49, .occ 50, .occ 51, .occ 53, .occ 55, .occ 57, .occ 59, .occ 62, .occ 63, .occ 66, .occ 67, .occ 68, .occ 69, .occ 71, .occ 72, .occ 73, .occ 74, .occ 75, .occ 76, .occ 79, .sumGe, .nonneg 0, .nonneg 6, .nonneg 8, .nonneg 10, .nonneg 35, .nonneg 36, .nonneg 37, .nonneg 39, .nonneg 41, .nonneg 42, .nonneg 45, .nonneg 52, .branchGe 57 (1)]

def plane467GenLeaf0003Mult : Fin 60 → Nat := ![1797, 555, 249, 117, 685, 21, 1223, 1457, 258, 216, 4186, 2185, 382, 1086, 796, 596, 2001, 636, 664, 891, 650, 1483, 366, 1392, 1243, 2731, 2703, 2279, 786, 170, 1244, 1478, 1248, 523, 639, 1394, 740, 571, 1115, 64, 286, 990, 36, 766, 546, 1312, 5498, 1248, 772, 926, 6400, 2422, 3006, 2904, 2128, 3554, 1362, 2904, 2900, 11312]

theorem plane467GenLeaf0003 (x : Fin 59 → Int)
    (hroot : plane467GenOccSys.RootHolds x)
    (hLB_57 : (1 : Int) ≤ x 57)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane467GenLeaf0003Refs i).resolveCoeff plane467GenOccSys j)
    (fun i => (plane467GenLeaf0003Refs i).resolveRhs plane467GenOccSys) plane467GenLeaf0003Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane467GenLeaf0003Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 4
  · exact hroot.hOcc 5
  · exact hroot.hOcc 7
  · exact hroot.hOcc 8
  · exact hroot.hOcc 9
  · exact hroot.hOcc 10
  · exact hroot.hOcc 11
  · exact hroot.hOcc 13
  · exact hroot.hOcc 16
  · exact hroot.hOcc 17
  · exact hroot.hOcc 18
  · exact hroot.hOcc 21
  · exact hroot.hOcc 23
  · exact hroot.hOcc 24
  · exact hroot.hOcc 29
  · exact hroot.hOcc 32
  · exact hroot.hOcc 34
  · exact hroot.hOcc 37
  · exact hroot.hOcc 38
  · exact hroot.hOcc 41
  · exact hroot.hOcc 42
  · exact hroot.hOcc 43
  · exact hroot.hOcc 45
  · exact hroot.hOcc 46
  · exact hroot.hOcc 47
  · exact hroot.hOcc 48
  · exact hroot.hOcc 49
  · exact hroot.hOcc 50
  · exact hroot.hOcc 51
  · exact hroot.hOcc 53
  · exact hroot.hOcc 55
  · exact hroot.hOcc 57
  · exact hroot.hOcc 59
  · exact hroot.hOcc 62
  · exact hroot.hOcc 63
  · exact hroot.hOcc 66
  · exact hroot.hOcc 67
  · exact hroot.hOcc 68
  · exact hroot.hOcc 69
  · exact hroot.hOcc 71
  · exact hroot.hOcc 72
  · exact hroot.hOcc 73
  · exact hroot.hOcc 74
  · exact hroot.hOcc 75
  · exact hroot.hOcc 76
  · exact hroot.hOcc 79
  · change (∑ j, (-1 : Int) * x j) ≤ -plane467GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (6 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (8 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (10 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (35 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 35
  · change (∑ k, (if k = (36 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (37 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (39 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (41 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (42 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (45 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (52 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (57 : Fin 59) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_57

end QiushiMatmul
