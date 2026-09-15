import QiushiPlane453GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane453GenLeaf0004Refs : Fin 51 → RowRef 210 50 := ![.occ 18, .occ 20, .occ 22, .occ 38, .occ 45, .occ 46, .occ 52, .occ 60, .occ 62, .occ 68, .occ 69, .occ 70, .occ 71, .occ 74, .occ 93, .occ 96, .occ 97, .occ 98, .occ 100, .occ 102, .occ 103, .occ 105, .occ 106, .occ 126, .occ 135, .occ 137, .occ 139, .occ 157, .occ 164, .occ 166, .occ 167, .occ 169, .occ 196, .occ 198, .occ 202, .occ 204, .occ 205, .occ 207, .occ 209, .sumGe, .nonneg 0, .nonneg 22, .nonneg 28, .nonneg 31, .nonneg 37, .nonneg 44, .nonneg 47, .branchLe 35 (0), .branchLe 5 (1), .branchGe 15 (1), .branchGe 17 (1)]

def plane453GenLeaf0004Mult : Fin 51 → Nat := ![28, 144, 1680, 1860, 212, 656, 2224, 1328, 64, 976, 1324, 2944, 648, 444, 196, 792, 204, 1192, 876, 572, 280, 496, 592, 206, 1096, 96, 912, 1242, 166, 2170, 440, 1704, 1039, 113, 757, 367, 514, 770, 536, 5072, 1688, 516, 1888, 1128, 1128, 344, 2608, 4500, 2084, 4032, 14556]

theorem plane453GenLeaf0004 (x : Fin 50 → Int)
    (hroot : plane453GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hUB_35 : x 35 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (1 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane453GenLeaf0004Refs i).resolveCoeff plane453GenOccSys j)
    (fun i => (plane453GenLeaf0004Refs i).resolveRhs plane453GenOccSys) plane453GenLeaf0004Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane453GenLeaf0004Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 18
  · exact hroot.hOcc 20
  · exact hroot.hOcc 22
  · exact hroot.hOcc 38
  · exact hroot.hOcc 45
  · exact hroot.hOcc 46
  · exact hroot.hOcc 52
  · exact hroot.hOcc 60
  · exact hroot.hOcc 62
  · exact hroot.hOcc 68
  · exact hroot.hOcc 69
  · exact hroot.hOcc 70
  · exact hroot.hOcc 71
  · exact hroot.hOcc 74
  · exact hroot.hOcc 93
  · exact hroot.hOcc 96
  · exact hroot.hOcc 97
  · exact hroot.hOcc 98
  · exact hroot.hOcc 100
  · exact hroot.hOcc 102
  · exact hroot.hOcc 103
  · exact hroot.hOcc 105
  · exact hroot.hOcc 106
  · exact hroot.hOcc 126
  · exact hroot.hOcc 135
  · exact hroot.hOcc 137
  · exact hroot.hOcc 139
  · exact hroot.hOcc 157
  · exact hroot.hOcc 164
  · exact hroot.hOcc 166
  · exact hroot.hOcc 167
  · exact hroot.hOcc 169
  · exact hroot.hOcc 196
  · exact hroot.hOcc 198
  · exact hroot.hOcc 202
  · exact hroot.hOcc 204
  · exact hroot.hOcc 205
  · exact hroot.hOcc 207
  · exact hroot.hOcc 209
  · change (∑ j, (-1 : Int) * x j) ≤ -plane453GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (22 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (28 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (31 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 31
  · change (∑ k, (if k = (37 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (44 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (47 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (35 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (5 : Fin 50) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (15 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (17 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17

end QiushiMatmul
