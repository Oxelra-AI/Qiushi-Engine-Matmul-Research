import QiushiPlane275GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane275GenLeaf0000Refs : Fin 8 → RowRef 29 9 := ![.occ 22, .occ 23, .occ 24, .occ 25, .occ 26, .occ 27, .occ 28, .sumGe]

def plane275GenLeaf0000Mult : Fin 8 → Nat := ![1, 1, 2, 1, 1, 1, 1, 2]

theorem plane275GenLeaf0000 (x : Fin 9 → Int)
    (hroot : plane275GenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane275GenLeaf0000Refs i).resolveCoeff plane275GenOccSys j)
    (fun i => (plane275GenLeaf0000Refs i).resolveRhs plane275GenOccSys) plane275GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane275GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 22
  · exact hroot.hOcc 23
  · exact hroot.hOcc 24
  · exact hroot.hOcc 25
  · exact hroot.hOcc 26
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · change (∑ j, (-1 : Int) * x j) ≤ -plane275GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
