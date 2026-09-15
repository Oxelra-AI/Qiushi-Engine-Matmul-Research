import QiushiPlane453GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane453GenLeaf0011Refs : Fin 51 → RowRef 210 50 := ![.occ 18, .occ 27, .occ 31, .occ 32, .occ 36, .occ 43, .occ 49, .occ 53, .occ 58, .occ 63, .occ 65, .occ 66, .occ 70, .occ 76, .occ 77, .occ 84, .occ 86, .occ 91, .occ 92, .occ 101, .occ 102, .occ 104, .occ 105, .occ 114, .occ 115, .occ 121, .occ 131, .occ 140, .occ 142, .occ 144, .occ 148, .occ 158, .occ 161, .occ 162, .occ 166, .occ 169, .occ 170, .occ 205, .occ 208, .sumGe, .nonneg 19, .nonneg 22, .nonneg 23, .nonneg 24, .nonneg 26, .nonneg 28, .nonneg 29, .nonneg 33, .nonneg 43, .nonneg 45, .branchGe 35 (1)]

def plane453GenLeaf0011Mult : Fin 51 → Nat := ![5710, 1783, 6755, 8552, 1433, 583, 2361, 7917, 661, 524, 1348, 2127, 1248, 90, 6521, 7103, 4770, 1913, 60, 422, 7567, 958, 16, 1616, 5444, 94, 5783, 2295, 654, 2327, 717, 1355, 1565, 332, 830, 448, 6721, 432, 896, 9896, 1213, 1441, 210, 8967, 194, 288, 1221, 100, 398, 1417, 64455]

theorem plane453GenLeaf0011 (x : Fin 50 → Int)
    (hroot : plane453GenOccSys.RootHolds x)
    (hLB_35 : (1 : Int) ≤ x 35)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane453GenLeaf0011Refs i).resolveCoeff plane453GenOccSys j)
    (fun i => (plane453GenLeaf0011Refs i).resolveRhs plane453GenOccSys) plane453GenLeaf0011Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane453GenLeaf0011Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 18
  · exact hroot.hOcc 27
  · exact hroot.hOcc 31
  · exact hroot.hOcc 32
  · exact hroot.hOcc 36
  · exact hroot.hOcc 43
  · exact hroot.hOcc 49
  · exact hroot.hOcc 53
  · exact hroot.hOcc 58
  · exact hroot.hOcc 63
  · exact hroot.hOcc 65
  · exact hroot.hOcc 66
  · exact hroot.hOcc 70
  · exact hroot.hOcc 76
  · exact hroot.hOcc 77
  · exact hroot.hOcc 84
  · exact hroot.hOcc 86
  · exact hroot.hOcc 91
  · exact hroot.hOcc 92
  · exact hroot.hOcc 101
  · exact hroot.hOcc 102
  · exact hroot.hOcc 104
  · exact hroot.hOcc 105
  · exact hroot.hOcc 114
  · exact hroot.hOcc 115
  · exact hroot.hOcc 121
  · exact hroot.hOcc 131
  · exact hroot.hOcc 140
  · exact hroot.hOcc 142
  · exact hroot.hOcc 144
  · exact hroot.hOcc 148
  · exact hroot.hOcc 158
  · exact hroot.hOcc 161
  · exact hroot.hOcc 162
  · exact hroot.hOcc 166
  · exact hroot.hOcc 169
  · exact hroot.hOcc 170
  · exact hroot.hOcc 205
  · exact hroot.hOcc 208
  · change (∑ j, (-1 : Int) * x j) ≤ -plane453GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (19 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (22 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (23 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (24 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (26 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (28 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (29 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (33 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (43 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 43
  · change (∑ k, (if k = (45 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (35 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35

end QiushiMatmul
