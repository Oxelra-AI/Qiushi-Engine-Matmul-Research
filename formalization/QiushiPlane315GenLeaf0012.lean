import QiushiPlane315GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane315GenLeaf0012Refs : Fin 26 → RowRef 74 28 := ![.occ 6, .occ 7, .occ 8, .occ 13, .occ 15, .occ 17, .occ 21, .occ 28, .occ 34, .occ 35, .occ 37, .occ 41, .occ 44, .occ 45, .occ 47, .occ 52, .occ 56, .occ 58, .occ 63, .occ 67, .sumGe, .nonneg 6, .nonneg 17, .nonneg 19, .branchGe 5 (1), .branchLe 1 (0)]

def plane315GenLeaf0012Mult : Fin 26 → Nat := ![10, 2, 4, 4, 4, 4, 4, 7, 1, 3, 6, 3, 2, 2, 3, 2, 9, 4, 1, 7, 14, 2, 6, 12, 22, 12]

theorem plane315GenLeaf0012 (x : Fin 28 → Int)
    (hroot : plane315GenOccSys.RootHolds x)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hUB_1 : x 1 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane315GenLeaf0012Refs i).resolveCoeff plane315GenOccSys j)
    (fun i => (plane315GenLeaf0012Refs i).resolveRhs plane315GenOccSys) plane315GenLeaf0012Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane315GenLeaf0012Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 6
  · exact hroot.hOcc 7
  · exact hroot.hOcc 8
  · exact hroot.hOcc 13
  · exact hroot.hOcc 15
  · exact hroot.hOcc 17
  · exact hroot.hOcc 21
  · exact hroot.hOcc 28
  · exact hroot.hOcc 34
  · exact hroot.hOcc 35
  · exact hroot.hOcc 37
  · exact hroot.hOcc 41
  · exact hroot.hOcc 44
  · exact hroot.hOcc 45
  · exact hroot.hOcc 47
  · exact hroot.hOcc 52
  · exact hroot.hOcc 56
  · exact hroot.hOcc 58
  · exact hroot.hOcc 63
  · exact hroot.hOcc 67
  · change (∑ j, (-1 : Int) * x j) ≤ -plane315GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (17 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (19 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (5 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5
  · change (∑ k, (if k = (1 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1

end QiushiMatmul
