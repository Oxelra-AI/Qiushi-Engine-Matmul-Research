import QiushiPlane467GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane467GenLeaf0001Refs : Fin 49 → RowRef 84 59 := ![.occ 6, .occ 12, .occ 15, .occ 18, .occ 20, .occ 21, .occ 22, .occ 24, .occ 25, .occ 26, .occ 27, .occ 28, .occ 29, .occ 31, .occ 34, .occ 36, .occ 37, .occ 39, .occ 41, .occ 43, .occ 45, .occ 46, .occ 48, .occ 51, .occ 54, .occ 55, .occ 57, .occ 58, .occ 60, .occ 61, .occ 62, .occ 63, .occ 65, .occ 67, .occ 69, .sumGe, .nonneg 10, .nonneg 34, .nonneg 35, .nonneg 36, .nonneg 37, .nonneg 41, .nonneg 42, .nonneg 44, .nonneg 45, .nonneg 49, .nonneg 55, .branchLe 57 (0), .branchGe 24 (1)]

def plane467GenLeaf0001Mult : Fin 49 → Nat := ![14, 12, 16, 34, 6, 7, 6, 14, 11, 2, 4, 4, 6, 14, 1, 4, 16, 19, 11, 9, 8, 3, 4, 9, 8, 16, 4, 6, 2, 4, 12, 6, 6, 6, 4, 34, 40, 8, 28, 10, 6, 22, 30, 6, 8, 12, 10, 18, 42]

theorem plane467GenLeaf0001 (x : Fin 59 → Int)
    (hroot : plane467GenOccSys.RootHolds x)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hUB_57 : x 57 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane467GenLeaf0001Refs i).resolveCoeff plane467GenOccSys j)
    (fun i => (plane467GenLeaf0001Refs i).resolveRhs plane467GenOccSys) plane467GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane467GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 6
  · exact hroot.hOcc 12
  · exact hroot.hOcc 15
  · exact hroot.hOcc 18
  · exact hroot.hOcc 20
  · exact hroot.hOcc 21
  · exact hroot.hOcc 22
  · exact hroot.hOcc 24
  · exact hroot.hOcc 25
  · exact hroot.hOcc 26
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · exact hroot.hOcc 29
  · exact hroot.hOcc 31
  · exact hroot.hOcc 34
  · exact hroot.hOcc 36
  · exact hroot.hOcc 37
  · exact hroot.hOcc 39
  · exact hroot.hOcc 41
  · exact hroot.hOcc 43
  · exact hroot.hOcc 45
  · exact hroot.hOcc 46
  · exact hroot.hOcc 48
  · exact hroot.hOcc 51
  · exact hroot.hOcc 54
  · exact hroot.hOcc 55
  · exact hroot.hOcc 57
  · exact hroot.hOcc 58
  · exact hroot.hOcc 60
  · exact hroot.hOcc 61
  · exact hroot.hOcc 62
  · exact hroot.hOcc 63
  · exact hroot.hOcc 65
  · exact hroot.hOcc 67
  · exact hroot.hOcc 69
  · change (∑ j, (-1 : Int) * x j) ≤ -plane467GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (34 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 34
  · change (∑ k, (if k = (35 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 35
  · change (∑ k, (if k = (36 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (37 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (41 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (42 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (44 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (45 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (49 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (55 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (57 : Fin 59) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_57
  · change (∑ k, (if k = (24 : Fin 59) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24

end QiushiMatmul
