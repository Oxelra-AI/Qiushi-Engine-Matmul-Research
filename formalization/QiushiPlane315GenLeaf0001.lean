import QiushiPlane315GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane315GenLeaf0001Refs : Fin 27 → RowRef 74 28 := ![.occ 3, .occ 5, .occ 7, .occ 10, .occ 12, .occ 13, .occ 16, .occ 21, .occ 26, .occ 30, .occ 31, .occ 38, .occ 41, .occ 44, .occ 45, .occ 47, .occ 52, .occ 53, .occ 58, .occ 67, .sumGe, .nonneg 6, .nonneg 17, .branchLe 5 (0), .branchLe 2 (0), .branchLe 4 (1), .branchLe 0 (1)]

def plane315GenLeaf0001Mult : Fin 27 → Nat := ![1, 7, 1, 2, 1, 3, 3, 1, 1, 2, 6, 1, 2, 1, 2, 6, 4, 1, 3, 4, 10, 7, 1, 5, 10, 6, 6]

theorem plane315GenLeaf0001 (x : Fin 28 → Int)
    (hroot : plane315GenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (1 : Int))
    (hUB_0 : x 0 ≤ (1 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane315GenLeaf0001Refs i).resolveCoeff plane315GenOccSys j)
    (fun i => (plane315GenLeaf0001Refs i).resolveRhs plane315GenOccSys) plane315GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane315GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 3
  · exact hroot.hOcc 5
  · exact hroot.hOcc 7
  · exact hroot.hOcc 10
  · exact hroot.hOcc 12
  · exact hroot.hOcc 13
  · exact hroot.hOcc 16
  · exact hroot.hOcc 21
  · exact hroot.hOcc 26
  · exact hroot.hOcc 30
  · exact hroot.hOcc 31
  · exact hroot.hOcc 38
  · exact hroot.hOcc 41
  · exact hroot.hOcc 44
  · exact hroot.hOcc 45
  · exact hroot.hOcc 47
  · exact hroot.hOcc 52
  · exact hroot.hOcc 53
  · exact hroot.hOcc 58
  · exact hroot.hOcc 67
  · change (∑ j, (-1 : Int) * x j) ≤ -plane315GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (17 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (5 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (2 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (4 : Fin 28) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (0 : Fin 28) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_0

end QiushiMatmul
