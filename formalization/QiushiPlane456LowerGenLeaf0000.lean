import QiushiPlane456LowerGenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane456LowerGenLeaf0000Refs : Fin 2 → RowRef 50 3 := ![.occ 49, .sumGe]

def plane456LowerGenLeaf0000Mult : Fin 2 → Nat := ![1, 1]

theorem plane456LowerGenLeaf0000 (x : Fin 3 → Int)
    (hroot : plane456LowerGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane456LowerGenLeaf0000Refs i).resolveCoeff plane456LowerGenOccSys j)
    (fun i => (plane456LowerGenLeaf0000Refs i).resolveRhs plane456LowerGenOccSys) plane456LowerGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane456LowerGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 49
  · change (∑ j, (-1 : Int) * x j) ≤ -plane456LowerGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
