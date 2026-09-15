import QiushiPlane470LowerGenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane470LowerGenLeaf0000Refs : Fin 3 → RowRef 52 5 := ![.occ 50, .occ 51, .sumGe]

def plane470LowerGenLeaf0000Mult : Fin 3 → Nat := ![1, 1, 1]

theorem plane470LowerGenLeaf0000 (x : Fin 5 → Int)
    (hroot : plane470LowerGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane470LowerGenLeaf0000Refs i).resolveCoeff plane470LowerGenOccSys j)
    (fun i => (plane470LowerGenLeaf0000Refs i).resolveRhs plane470LowerGenOccSys) plane470LowerGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane470LowerGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 50
  · exact hroot.hOcc 51
  · change (∑ j, (-1 : Int) * x j) ≤ -plane470LowerGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
