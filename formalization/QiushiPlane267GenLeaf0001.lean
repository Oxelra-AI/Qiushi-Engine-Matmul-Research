import QiushiPlane267GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane267GenLeaf0001Refs : Fin 11 → RowRef 33 20 := ![.occ 12, .occ 15, .occ 16, .occ 22, .occ 23, .occ 25, .occ 26, .occ 31, .occ 32, .sumGe, .branchGe 10 (1)]

def plane267GenLeaf0001Mult : Fin 11 → Nat := ![4, 1, 3, 3, 1, 3, 1, 3, 1, 4, 8]

theorem plane267GenLeaf0001 (x : Fin 20 → Int)
    (hroot : plane267GenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane267GenLeaf0001Refs i).resolveCoeff plane267GenOccSys j)
    (fun i => (plane267GenLeaf0001Refs i).resolveRhs plane267GenOccSys) plane267GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane267GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 12
  · exact hroot.hOcc 15
  · exact hroot.hOcc 16
  · exact hroot.hOcc 22
  · exact hroot.hOcc 23
  · exact hroot.hOcc 25
  · exact hroot.hOcc 26
  · exact hroot.hOcc 31
  · exact hroot.hOcc 32
  · change (∑ j, (-1 : Int) * x j) ≤ -plane267GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 20) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10

end QiushiMatmul
