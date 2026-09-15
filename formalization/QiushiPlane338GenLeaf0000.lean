import QiushiPlane338GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane338GenLeaf0000Refs : Fin 7 → RowRef 21 16 := ![.occ 15, .occ 16, .occ 17, .occ 18, .occ 19, .occ 20, .sumGe]

def plane338GenLeaf0000Mult : Fin 7 → Nat := ![1, 1, 1, 1, 1, 1, 1]

theorem plane338GenLeaf0000 (x : Fin 16 → Int)
    (hroot : plane338GenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane338GenLeaf0000Refs i).resolveCoeff plane338GenOccSys j)
    (fun i => (plane338GenLeaf0000Refs i).resolveRhs plane338GenOccSys) plane338GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane338GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 15
  · exact hroot.hOcc 16
  · exact hroot.hOcc 17
  · exact hroot.hOcc 18
  · exact hroot.hOcc 19
  · exact hroot.hOcc 20
  · change (∑ j, (-1 : Int) * x j) ≤ -plane338GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
