import QiushiPlane152GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane152GenLeaf0001Refs : Fin 7 → RowRef 16 10 := ![.occ 5, .occ 10, .occ 11, .occ 12, .occ 13, .sumGe, .branchGe 0 (2)]

def plane152GenLeaf0001Mult : Fin 7 → Nat := ![2, 1, 1, 1, 1, 2, 2]

theorem plane152GenLeaf0001 (x : Fin 10 → Int)
    (hroot : plane152GenOccSys.RootHolds x)
    (hLB_0 : (2 : Int) ≤ x 0)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane152GenLeaf0001Refs i).resolveCoeff plane152GenOccSys j)
    (fun i => (plane152GenLeaf0001Refs i).resolveRhs plane152GenOccSys) plane152GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane152GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · exact hroot.hOcc 10
  · exact hroot.hOcc 11
  · exact hroot.hOcc 12
  · exact hroot.hOcc 13
  · change (∑ j, (-1 : Int) * x j) ≤ -plane152GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 10) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
