import QiushiPlane475GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane475GenLeaf0001Refs : Fin 57 → RowRef 126 56 := ![.occ 8, .occ 9, .occ 12, .occ 13, .occ 17, .occ 19, .occ 23, .occ 24, .occ 29, .occ 35, .occ 37, .occ 38, .occ 40, .occ 42, .occ 45, .occ 46, .occ 48, .occ 50, .occ 56, .occ 58, .occ 59, .occ 61, .occ 62, .occ 63, .occ 65, .occ 67, .occ 69, .occ 72, .occ 73, .occ 74, .occ 76, .occ 77, .occ 78, .occ 80, .occ 81, .occ 84, .occ 86, .occ 90, .occ 101, .occ 102, .occ 105, .occ 113, .occ 117, .occ 122, .occ 123, .sumGe, .nonneg 0, .nonneg 7, .nonneg 8, .nonneg 10, .nonneg 12, .nonneg 22, .nonneg 24, .nonneg 35, .nonneg 37, .branchLe 34 (0), .branchGe 2 (1)]

def plane475GenLeaf0001Mult : Fin 57 → Nat := ![9110, 9859, 137215, 2368, 14820, 9685, 7979, 28789, 18865, 6910, 57796, 22811, 8958, 32872, 114689, 91377, 92622, 37137, 34410, 38217, 39874, 9443, 1645, 55447, 12277, 33662, 844, 21437, 58609, 26785, 22568, 19055, 51984, 3498, 7571, 43625, 12766, 11464, 74468, 18281, 16512, 58193, 4268, 5388, 72322, 183999, 37908, 19280, 29506, 63322, 297556, 73357, 16242, 31471, 117028, 183999, 529532]

theorem plane475GenLeaf0001 (x : Fin 56 → Int)
    (hroot : plane475GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane475GenLeaf0001Refs i).resolveCoeff plane475GenOccSys j)
    (fun i => (plane475GenLeaf0001Refs i).resolveRhs plane475GenOccSys) plane475GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane475GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 8
  · exact hroot.hOcc 9
  · exact hroot.hOcc 12
  · exact hroot.hOcc 13
  · exact hroot.hOcc 17
  · exact hroot.hOcc 19
  · exact hroot.hOcc 23
  · exact hroot.hOcc 24
  · exact hroot.hOcc 29
  · exact hroot.hOcc 35
  · exact hroot.hOcc 37
  · exact hroot.hOcc 38
  · exact hroot.hOcc 40
  · exact hroot.hOcc 42
  · exact hroot.hOcc 45
  · exact hroot.hOcc 46
  · exact hroot.hOcc 48
  · exact hroot.hOcc 50
  · exact hroot.hOcc 56
  · exact hroot.hOcc 58
  · exact hroot.hOcc 59
  · exact hroot.hOcc 61
  · exact hroot.hOcc 62
  · exact hroot.hOcc 63
  · exact hroot.hOcc 65
  · exact hroot.hOcc 67
  · exact hroot.hOcc 69
  · exact hroot.hOcc 72
  · exact hroot.hOcc 73
  · exact hroot.hOcc 74
  · exact hroot.hOcc 76
  · exact hroot.hOcc 77
  · exact hroot.hOcc 78
  · exact hroot.hOcc 80
  · exact hroot.hOcc 81
  · exact hroot.hOcc 84
  · exact hroot.hOcc 86
  · exact hroot.hOcc 90
  · exact hroot.hOcc 101
  · exact hroot.hOcc 102
  · exact hroot.hOcc 105
  · exact hroot.hOcc 113
  · exact hroot.hOcc 117
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · change (∑ j, (-1 : Int) * x j) ≤ -plane475GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (7 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (8 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (10 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (12 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (22 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (24 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (35 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 35
  · change (∑ k, (if k = (37 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (34 : Fin 56) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (2 : Fin 56) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2

end QiushiMatmul
