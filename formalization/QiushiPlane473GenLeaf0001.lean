import QiushiPlane473GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane473GenLeaf0001Refs : Fin 60 → RowRef 153 59 := ![.occ 4, .occ 15, .occ 21, .occ 30, .occ 31, .occ 33, .occ 34, .occ 35, .occ 36, .occ 37, .occ 38, .occ 39, .occ 41, .occ 44, .occ 45, .occ 46, .occ 51, .occ 52, .occ 54, .occ 55, .occ 56, .occ 58, .occ 59, .occ 61, .occ 63, .occ 66, .occ 70, .occ 71, .occ 75, .occ 78, .occ 79, .occ 80, .occ 81, .occ 84, .occ 88, .occ 92, .occ 97, .occ 109, .occ 111, .occ 116, .occ 117, .occ 119, .occ 120, .occ 123, .occ 130, .occ 132, .occ 136, .occ 139, .occ 143, .occ 145, .occ 146, .occ 151, .sumGe, .nonneg 3, .nonneg 16, .nonneg 36, .branchLe 40 (0), .branchLe 14 (0), .branchLe 44 (0), .branchGe 20 (1)]

def plane473GenLeaf0001Mult : Fin 60 → Nat := ![150960, 147412, 77304, 88842, 50216, 76124, 5628, 20204, 65831, 210240, 117669, 5285, 64175, 72022, 46346, 48086, 29022, 70778, 53989, 18536, 39254, 20698, 43805, 3103, 68604, 21159, 28322, 15657, 21812, 49236, 61193, 2482, 31044, 40420, 113798, 56152, 14882, 83242, 14050, 27755, 84232, 34850, 29174, 100718, 36167, 7354, 4563, 62776, 19070, 19170, 38613, 31795, 351218, 214289, 309741, 145206, 243206, 283256, 93258, 1132241]

theorem plane473GenLeaf0001 (x : Fin 59 → Int)
    (hroot : plane473GenOccSys.RootHolds x)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hUB_40 : x 40 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_44 : x 44 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane473GenLeaf0001Refs i).resolveCoeff plane473GenOccSys j)
    (fun i => (plane473GenLeaf0001Refs i).resolveRhs plane473GenOccSys) plane473GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane473GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 4
  · exact hroot.hOcc 15
  · exact hroot.hOcc 21
  · exact hroot.hOcc 30
  · exact hroot.hOcc 31
  · exact hroot.hOcc 33
  · exact hroot.hOcc 34
  · exact hroot.hOcc 35
  · exact hroot.hOcc 36
  · exact hroot.hOcc 37
  · exact hroot.hOcc 38
  · exact hroot.hOcc 39
  · exact hroot.hOcc 41
  · exact hroot.hOcc 44
  · exact hroot.hOcc 45
  · exact hroot.hOcc 46
  · exact hroot.hOcc 51
  · exact hroot.hOcc 52
  · exact hroot.hOcc 54
  · exact hroot.hOcc 55
  · exact hroot.hOcc 56
  · exact hroot.hOcc 58
  · exact hroot.hOcc 59
  · exact hroot.hOcc 61
  · exact hroot.hOcc 63
  · exact hroot.hOcc 66
  · exact hroot.hOcc 70
  · exact hroot.hOcc 71
  · exact hroot.hOcc 75
  · exact hroot.hOcc 78
  · exact hroot.hOcc 79
  · exact hroot.hOcc 80
  · exact hroot.hOcc 81
  · exact hroot.hOcc 84
  · exact hroot.hOcc 88
  · exact hroot.hOcc 92
  · exact hroot.hOcc 97
  · exact hroot.hOcc 109
  · exact hroot.hOcc 111
  · exact hroot.hOcc 116
  · exact hroot.hOcc 117
  · exact hroot.hOcc 119
  · exact hroot.hOcc 120
  · exact hroot.hOcc 123
  · exact hroot.hOcc 130
  · exact hroot.hOcc 132
  · exact hroot.hOcc 136
  · exact hroot.hOcc 139
  · exact hroot.hOcc 143
  · exact hroot.hOcc 145
  · exact hroot.hOcc 146
  · exact hroot.hOcc 151
  · change (∑ j, (-1 : Int) * x j) ≤ -plane473GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (16 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (36 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (40 : Fin 59) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (14 : Fin 59) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (44 : Fin 59) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (20 : Fin 59) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20

end QiushiMatmul
