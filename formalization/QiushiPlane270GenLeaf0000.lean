import QiushiPlane270GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane270GenLeaf0000Refs : Fin 3 → RowRef 22 11 := ![.occ 20, .occ 21, .sumGe]

def plane270GenLeaf0000Mult : Fin 3 → Nat := ![1, 1, 1]

theorem plane270GenLeaf0000 (x : Fin 11 → Int)
    (hroot : plane270GenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane270GenLeaf0000Refs i).resolveCoeff plane270GenOccSys j)
    (fun i => (plane270GenLeaf0000Refs i).resolveRhs plane270GenOccSys) plane270GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane270GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 20
  · exact hroot.hOcc 21
  · change (∑ j, (-1 : Int) * x j) ≤ -plane270GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
