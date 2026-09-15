import QiushiPlane269GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane269GenLeaf0001Refs : Fin 9 → RowRef 30 21 := ![.occ 10, .occ 11, .occ 12, .occ 13, .occ 25, .occ 26, .occ 29, .sumGe, .branchGe 0 (3)]

def plane269GenLeaf0001Mult : Fin 9 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 4]

theorem plane269GenLeaf0001 (x : Fin 21 → Int)
    (hroot : plane269GenOccSys.RootHolds x)
    (hLB_0 : (3 : Int) ≤ x 0)
    (hUB_1 : x 1 ≤ (1 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane269GenLeaf0001Refs i).resolveCoeff plane269GenOccSys j)
    (fun i => (plane269GenLeaf0001Refs i).resolveRhs plane269GenOccSys) plane269GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane269GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 10
  · exact hroot.hOcc 11
  · exact hroot.hOcc 12
  · exact hroot.hOcc 13
  · exact hroot.hOcc 25
  · exact hroot.hOcc 26
  · exact hroot.hOcc 29
  · change (∑ j, (-1 : Int) * x j) ≤ -plane269GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 21) then (-1 : Int) else 0) * x k) ≤ -(3 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
