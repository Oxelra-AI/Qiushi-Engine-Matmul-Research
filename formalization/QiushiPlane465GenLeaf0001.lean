import QiushiPlane465GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane465GenLeaf0001Refs : Fin 58 → RowRef 88 57 := ![.occ 8, .occ 11, .occ 12, .occ 13, .occ 14, .occ 15, .occ 16, .occ 17, .occ 20, .occ 21, .occ 22, .occ 23, .occ 24, .occ 25, .occ 27, .occ 28, .occ 29, .occ 30, .occ 31, .occ 32, .occ 33, .occ 34, .occ 35, .occ 36, .occ 39, .occ 40, .occ 44, .occ 45, .occ 46, .occ 48, .occ 49, .occ 50, .occ 51, .occ 52, .occ 53, .occ 54, .occ 55, .occ 57, .occ 59, .occ 60, .occ 61, .occ 62, .occ 66, .occ 71, .occ 72, .occ 73, .occ 78, .occ 79, .occ 81, .occ 86, .sumGe, .nonneg 0, .nonneg 19, .nonneg 37, .nonneg 51, .nonneg 54, .nonneg 56, .branchGe 44 (1)]

def plane465GenLeaf0001Mult : Fin 58 → Nat := ![2952, 3910, 6369, 1795, 1981, 5512, 4083, 1608, 1823, 4927, 504, 1894, 538, 466, 114, 1712, 2176, 2613, 2473, 1964, 1900, 1182, 4013, 1008, 1294, 178, 4156, 944, 534, 2061, 1494, 3692, 944, 2784, 3932, 1614, 1407, 426, 1543, 346, 91, 322, 1129, 2924, 423, 250, 1213, 386, 2155, 1295, 9008, 9032, 4512, 4464, 7326, 1492, 1588, 61326]

theorem plane465GenLeaf0001 (x : Fin 57 → Int)
    (hroot : plane465GenOccSys.RootHolds x)
    (hLB_44 : (1 : Int) ≤ x 44)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane465GenLeaf0001Refs i).resolveCoeff plane465GenOccSys j)
    (fun i => (plane465GenLeaf0001Refs i).resolveRhs plane465GenOccSys) plane465GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane465GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 8
  · exact hroot.hOcc 11
  · exact hroot.hOcc 12
  · exact hroot.hOcc 13
  · exact hroot.hOcc 14
  · exact hroot.hOcc 15
  · exact hroot.hOcc 16
  · exact hroot.hOcc 17
  · exact hroot.hOcc 20
  · exact hroot.hOcc 21
  · exact hroot.hOcc 22
  · exact hroot.hOcc 23
  · exact hroot.hOcc 24
  · exact hroot.hOcc 25
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · exact hroot.hOcc 29
  · exact hroot.hOcc 30
  · exact hroot.hOcc 31
  · exact hroot.hOcc 32
  · exact hroot.hOcc 33
  · exact hroot.hOcc 34
  · exact hroot.hOcc 35
  · exact hroot.hOcc 36
  · exact hroot.hOcc 39
  · exact hroot.hOcc 40
  · exact hroot.hOcc 44
  · exact hroot.hOcc 45
  · exact hroot.hOcc 46
  · exact hroot.hOcc 48
  · exact hroot.hOcc 49
  · exact hroot.hOcc 50
  · exact hroot.hOcc 51
  · exact hroot.hOcc 52
  · exact hroot.hOcc 53
  · exact hroot.hOcc 54
  · exact hroot.hOcc 55
  · exact hroot.hOcc 57
  · exact hroot.hOcc 59
  · exact hroot.hOcc 60
  · exact hroot.hOcc 61
  · exact hroot.hOcc 62
  · exact hroot.hOcc 66
  · exact hroot.hOcc 71
  · exact hroot.hOcc 72
  · exact hroot.hOcc 73
  · exact hroot.hOcc 78
  · exact hroot.hOcc 79
  · exact hroot.hOcc 81
  · exact hroot.hOcc 86
  · change (∑ j, (-1 : Int) * x j) ≤ -plane465GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 57) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (19 : Fin 57) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (37 : Fin 57) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (51 : Fin 57) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 51
  · change (∑ k, (if k = (54 : Fin 57) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 54
  · change (∑ k, (if k = (56 : Fin 57) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 56
  · change (∑ k, (if k = (44 : Fin 57) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_44

end QiushiMatmul
