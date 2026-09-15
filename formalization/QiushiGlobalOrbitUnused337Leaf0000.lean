import QiushiGlobalOrbitUnused337Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane337UnusedGenLeaf0000Refs : Fin 4 → RowRef 30 8 := ![.occ 22, .occ 24, .occ 28, .sumGe]

def plane337UnusedGenLeaf0000Mult : Fin 4 → Nat := ![1, 1, 1, 1]

theorem plane337UnusedGenLeaf0000 (x : Fin 8 → Int)
    (hroot : plane337UnusedGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane337UnusedGenLeaf0000Refs i).resolveCoeff plane337UnusedGenOccSys j)
    (fun i => (plane337UnusedGenLeaf0000Refs i).resolveRhs plane337UnusedGenOccSys) plane337UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane337UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 22
  · exact hroot.hOcc 24
  · exact hroot.hOcc 28
  · change (∑ j, (-1 : Int) * x j) ≤ -plane337UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
