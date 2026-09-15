import QiushiPlane477GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane477GenLeaf0000Refs : Fin 1 → RowRef 63 0 := ![.sumGe]

def plane477GenLeaf0000Mult : Fin 1 → Nat := ![1]

theorem plane477GenLeaf0000 (x : Fin 0 → Int)
    (hroot : plane477GenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane477GenLeaf0000Refs i).resolveCoeff plane477GenOccSys j)
    (fun i => (plane477GenLeaf0000Refs i).resolveRhs plane477GenOccSys) plane477GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane477GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · change (∑ j, (-1 : Int) * x j) ≤ -plane477GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
