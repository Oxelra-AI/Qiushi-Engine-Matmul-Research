import QiushiPlane459GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane459GenLeaf0000Refs : Fin 8 → RowRef 42 28 := ![.occ 35, .occ 36, .occ 37, .occ 38, .occ 39, .occ 40, .occ 41, .sumGe]

def plane459GenLeaf0000Mult : Fin 8 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1]

theorem plane459GenLeaf0000 (x : Fin 28 → Int)
    (hroot : plane459GenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane459GenLeaf0000Refs i).resolveCoeff plane459GenOccSys j)
    (fun i => (plane459GenLeaf0000Refs i).resolveRhs plane459GenOccSys) plane459GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane459GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 35
  · exact hroot.hOcc 36
  · exact hroot.hOcc 37
  · exact hroot.hOcc 38
  · exact hroot.hOcc 39
  · exact hroot.hOcc 40
  · exact hroot.hOcc 41
  · change (∑ j, (-1 : Int) * x j) ≤ -plane459GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
