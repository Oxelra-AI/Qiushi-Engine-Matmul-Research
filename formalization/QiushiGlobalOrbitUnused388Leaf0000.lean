import QiushiGlobalOrbitUnused388Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane388UnusedGenLeaf0000Refs : Fin 8 → RowRef 28 13 := ![.occ 1, .occ 2, .occ 4, .occ 22, .occ 23, .occ 24, .occ 27, .sumGe]

def plane388UnusedGenLeaf0000Mult : Fin 8 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1]

theorem plane388UnusedGenLeaf0000 (x : Fin 13 → Int)
    (hroot : plane388UnusedGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane388UnusedGenLeaf0000Refs i).resolveCoeff plane388UnusedGenOccSys j)
    (fun i => (plane388UnusedGenLeaf0000Refs i).resolveRhs plane388UnusedGenOccSys) plane388UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane388UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · exact hroot.hOcc 2
  · exact hroot.hOcc 4
  · exact hroot.hOcc 22
  · exact hroot.hOcc 23
  · exact hroot.hOcc 24
  · exact hroot.hOcc 27
  · change (∑ j, (-1 : Int) * x j) ≤ -plane388UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
