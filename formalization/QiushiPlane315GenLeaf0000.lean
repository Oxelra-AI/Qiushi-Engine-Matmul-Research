import QiushiPlane315GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane315GenLeaf0000Refs : Fin 28 → RowRef 74 28 := ![.occ 5, .occ 7, .occ 12, .occ 13, .occ 14, .occ 26, .occ 30, .occ 31, .occ 33, .occ 37, .occ 42, .occ 47, .occ 52, .occ 55, .occ 56, .occ 58, .occ 61, .occ 65, .occ 66, .occ 67, .occ 73, .sumGe, .nonneg 6, .nonneg 17, .nonneg 25, .branchLe 5 (0), .branchLe 2 (0), .branchLe 12 (0)]

def plane315GenLeaf0000Mult : Fin 28 → Nat := ![2, 12, 3, 10, 2, 2, 1, 6, 2, 6, 2, 7, 3, 4, 4, 6, 1, 1, 1, 8, 1, 17, 4, 1, 1, 5, 17, 15]

theorem plane315GenLeaf0000 (x : Fin 28 → Int)
    (hroot : plane315GenOccSys.RootHolds x)
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane315GenLeaf0000Refs i).resolveCoeff plane315GenOccSys j)
    (fun i => (plane315GenLeaf0000Refs i).resolveRhs plane315GenOccSys) plane315GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane315GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · exact hroot.hOcc 7
  · exact hroot.hOcc 12
  · exact hroot.hOcc 13
  · exact hroot.hOcc 14
  · exact hroot.hOcc 26
  · exact hroot.hOcc 30
  · exact hroot.hOcc 31
  · exact hroot.hOcc 33
  · exact hroot.hOcc 37
  · exact hroot.hOcc 42
  · exact hroot.hOcc 47
  · exact hroot.hOcc 52
  · exact hroot.hOcc 55
  · exact hroot.hOcc 56
  · exact hroot.hOcc 58
  · exact hroot.hOcc 61
  · exact hroot.hOcc 65
  · exact hroot.hOcc 66
  · exact hroot.hOcc 67
  · exact hroot.hOcc 73
  · change (∑ j, (-1 : Int) * x j) ≤ -plane315GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (17 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (25 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (5 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (2 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (12 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12

end QiushiMatmul
