import QiushiPlane282GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane282GenLeaf0036Refs : Fin 24 → RowRef 100 28 := ![.occ 4, .occ 9, .occ 10, .occ 13, .occ 34, .occ 37, .occ 41, .occ 42, .occ 43, .occ 60, .occ 63, .occ 65, .occ 66, .occ 69, .occ 74, .occ 87, .occ 88, .occ 89, .occ 90, .sumGe, .nonneg 18, .branchGe 12 (1), .branchGe 2 (2), .branchLe 0 (2)]

def plane282GenLeaf0036Mult : Fin 24 → Nat := ![8, 4, 2, 2, 2, 2, 4, 3, 1, 2, 4, 4, 1, 4, 8, 2, 2, 1, 2, 12, 2, 4, 16, 10]

theorem plane282GenLeaf0036 (x : Fin 28 → Int)
    (hroot : plane282GenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_2 : (2 : Int) ≤ x 2)
    (hUB_0 : x 0 ≤ (2 : Int))
    (hUB_8 : x 8 ≤ (1 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane282GenLeaf0036Refs i).resolveCoeff plane282GenOccSys j)
    (fun i => (plane282GenLeaf0036Refs i).resolveRhs plane282GenOccSys) plane282GenLeaf0036Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane282GenLeaf0036Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 4
  · exact hroot.hOcc 9
  · exact hroot.hOcc 10
  · exact hroot.hOcc 13
  · exact hroot.hOcc 34
  · exact hroot.hOcc 37
  · exact hroot.hOcc 41
  · exact hroot.hOcc 42
  · exact hroot.hOcc 43
  · exact hroot.hOcc 60
  · exact hroot.hOcc 63
  · exact hroot.hOcc 65
  · exact hroot.hOcc 66
  · exact hroot.hOcc 69
  · exact hroot.hOcc 74
  · exact hroot.hOcc 87
  · exact hroot.hOcc 88
  · exact hroot.hOcc 89
  · exact hroot.hOcc 90
  · change (∑ j, (-1 : Int) * x j) ≤ -plane282GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (18 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (12 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (2 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (0 : Fin 28) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_0

end QiushiMatmul
