import QiushiPlane315GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane315GenLeaf0002Refs : Fin 25 → RowRef 74 28 := ![.occ 3, .occ 5, .occ 7, .occ 12, .occ 13, .occ 16, .occ 21, .occ 37, .occ 41, .occ 45, .occ 47, .occ 52, .occ 55, .occ 58, .occ 67, .occ 72, .sumGe, .nonneg 3, .nonneg 6, .nonneg 17, .nonneg 19, .nonneg 25, .branchLe 2 (0), .branchLe 4 (1), .branchGe 0 (2)]

def plane315GenLeaf0002Mult : Fin 25 → Nat := ![5, 4, 5, 3, 7, 2, 2, 6, 3, 2, 5, 2, 1, 2, 7, 5, 12, 2, 7, 10, 3, 4, 12, 4, 6]

theorem plane315GenLeaf0002 (x : Fin 28 → Int)
    (hroot : plane315GenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_0 : (2 : Int) ≤ x 0)
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (1 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane315GenLeaf0002Refs i).resolveCoeff plane315GenOccSys j)
    (fun i => (plane315GenLeaf0002Refs i).resolveRhs plane315GenOccSys) plane315GenLeaf0002Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane315GenLeaf0002Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 3
  · exact hroot.hOcc 5
  · exact hroot.hOcc 7
  · exact hroot.hOcc 12
  · exact hroot.hOcc 13
  · exact hroot.hOcc 16
  · exact hroot.hOcc 21
  · exact hroot.hOcc 37
  · exact hroot.hOcc 41
  · exact hroot.hOcc 45
  · exact hroot.hOcc 47
  · exact hroot.hOcc 52
  · exact hroot.hOcc 55
  · exact hroot.hOcc 58
  · exact hroot.hOcc 67
  · exact hroot.hOcc 72
  · change (∑ j, (-1 : Int) * x j) ≤ -plane315GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (6 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (17 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (19 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (25 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (2 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (4 : Fin 28) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (0 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
