import QiushiPlane315GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane315GenLeaf0008Refs : Fin 20 → RowRef 74 28 := ![.occ 4, .occ 6, .occ 7, .occ 19, .occ 29, .occ 31, .occ 34, .occ 36, .occ 37, .occ 45, .occ 47, .occ 51, .occ 58, .occ 67, .sumGe, .nonneg 17, .nonneg 18, .branchLe 5 (0), .branchLe 10 (0), .branchGe 6 (1)]

def plane315GenLeaf0008Mult : Fin 20 → Nat := ![1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 7]

theorem plane315GenLeaf0008 (x : Fin 28 → Int)
    (hroot : plane315GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (1 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane315GenLeaf0008Refs i).resolveCoeff plane315GenOccSys j)
    (fun i => (plane315GenLeaf0008Refs i).resolveRhs plane315GenOccSys) plane315GenLeaf0008Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane315GenLeaf0008Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 4
  · exact hroot.hOcc 6
  · exact hroot.hOcc 7
  · exact hroot.hOcc 19
  · exact hroot.hOcc 29
  · exact hroot.hOcc 31
  · exact hroot.hOcc 34
  · exact hroot.hOcc 36
  · exact hroot.hOcc 37
  · exact hroot.hOcc 45
  · exact hroot.hOcc 47
  · exact hroot.hOcc 51
  · exact hroot.hOcc 58
  · exact hroot.hOcc 67
  · change (∑ j, (-1 : Int) * x j) ≤ -plane315GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (17 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (18 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (5 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (10 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (6 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6

end QiushiMatmul
