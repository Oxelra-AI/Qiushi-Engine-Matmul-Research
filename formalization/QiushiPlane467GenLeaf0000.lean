import QiushiPlane467GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane467GenLeaf0000Refs : Fin 58 → RowRef 84 59 := ![.occ 9, .occ 14, .occ 18, .occ 19, .occ 21, .occ 22, .occ 23, .occ 24, .occ 25, .occ 29, .occ 30, .occ 31, .occ 32, .occ 33, .occ 34, .occ 35, .occ 37, .occ 38, .occ 39, .occ 40, .occ 41, .occ 43, .occ 44, .occ 45, .occ 49, .occ 52, .occ 54, .occ 55, .occ 56, .occ 57, .occ 58, .occ 62, .occ 64, .occ 65, .occ 66, .occ 67, .occ 68, .occ 70, .occ 73, .occ 77, .occ 78, .sumGe, .nonneg 10, .nonneg 25, .nonneg 32, .nonneg 35, .nonneg 36, .nonneg 39, .nonneg 41, .nonneg 42, .nonneg 44, .nonneg 49, .nonneg 50, .nonneg 55, .nonneg 56, .branchLe 57 (0), .branchLe 7 (0), .branchLe 24 (0)]

def plane467GenLeaf0000Mult : Fin 58 → Nat := ![168, 420, 3847, 126, 863, 1531, 1031, 779, 755, 1053, 126, 86, 1364, 462, 275, 126, 821, 670, 948, 378, 2015, 948, 1137, 1448, 445, 98, 550, 966, 196, 672, 1029, 1200, 1058, 530, 876, 614, 1270, 378, 70, 434, 504, 4351, 6598, 714, 672, 3879, 2125, 84, 1923, 947, 252, 1050, 1470, 1890, 1428, 3234, 378, 3066]

theorem plane467GenLeaf0000 (x : Fin 59 → Int)
    (hroot : plane467GenOccSys.RootHolds x)
    (hUB_57 : x 57 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane467GenLeaf0000Refs i).resolveCoeff plane467GenOccSys j)
    (fun i => (plane467GenLeaf0000Refs i).resolveRhs plane467GenOccSys) plane467GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane467GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 9
  · exact hroot.hOcc 14
  · exact hroot.hOcc 18
  · exact hroot.hOcc 19
  · exact hroot.hOcc 21
  · exact hroot.hOcc 22
  · exact hroot.hOcc 23
  · exact hroot.hOcc 24
  · exact hroot.hOcc 25
  · exact hroot.hOcc 29
  · exact hroot.hOcc 30
  · exact hroot.hOcc 31
  · exact hroot.hOcc 32
  · exact hroot.hOcc 33
  · exact hroot.hOcc 34
  · exact hroot.hOcc 35
  · exact hroot.hOcc 37
  · exact hroot.hOcc 38
  · exact hroot.hOcc 39
  · exact hroot.hOcc 40
  · exact hroot.hOcc 41
  · exact hroot.hOcc 43
  · exact hroot.hOcc 44
  · exact hroot.hOcc 45
  · exact hroot.hOcc 49
  · exact hroot.hOcc 52
  · exact hroot.hOcc 54
  · exact hroot.hOcc 55
  · exact hroot.hOcc 56
  · exact hroot.hOcc 57
  · exact hroot.hOcc 58
  · exact hroot.hOcc 62
  · exact hroot.hOcc 64
  · exact hroot.hOcc 65
  · exact hroot.hOcc 66
  · exact hroot.hOcc 67
  · exact hroot.hOcc 68
  · exact hroot.hOcc 70
  · exact hroot.hOcc 73
  · exact hroot.hOcc 77
  · exact hroot.hOcc 78
  · change (∑ j, (-1 : Int) * x j) ≤ -plane467GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (25 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (32 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (35 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 35
  · change (∑ k, (if k = (36 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (39 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (41 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (42 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (44 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (49 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (50 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (55 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (56 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 56
  · change (∑ k, (if k = (57 : Fin 59) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_57
  · change (∑ k, (if k = (7 : Fin 59) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (24 : Fin 59) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24

end QiushiMatmul
