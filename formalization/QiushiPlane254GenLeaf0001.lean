import QiushiPlane254GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane254GenLeaf0001Refs : Fin 7 → RowRef 26 18 := ![.occ 13, .occ 14, .occ 21, .occ 24, .occ 25, .sumGe, .branchGe 0 (2)]

def plane254GenLeaf0001Mult : Fin 7 → Nat := ![1, 1, 1, 1, 1, 1, 4]

theorem plane254GenLeaf0001 (x : Fin 18 → Int)
    (hroot : plane254GenOccSys.RootHolds x)
    (hLB_0 : (2 : Int) ≤ x 0)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane254GenLeaf0001Refs i).resolveCoeff plane254GenOccSys j)
    (fun i => (plane254GenLeaf0001Refs i).resolveRhs plane254GenOccSys) plane254GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane254GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 13
  · exact hroot.hOcc 14
  · exact hroot.hOcc 21
  · exact hroot.hOcc 24
  · exact hroot.hOcc 25
  · change (∑ j, (-1 : Int) * x j) ≤ -plane254GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 18) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
