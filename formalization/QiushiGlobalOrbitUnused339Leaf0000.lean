import QiushiGlobalOrbitUnused339Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane339UnusedGenLeaf0000Refs : Fin 4 → RowRef 31 7 := ![.occ 24, .occ 26, .occ 30, .sumGe]

def plane339UnusedGenLeaf0000Mult : Fin 4 → Nat := ![1, 1, 1, 1]

theorem plane339UnusedGenLeaf0000 (x : Fin 7 → Int)
    (hroot : plane339UnusedGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane339UnusedGenLeaf0000Refs i).resolveCoeff plane339UnusedGenOccSys j)
    (fun i => (plane339UnusedGenLeaf0000Refs i).resolveRhs plane339UnusedGenOccSys) plane339UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane339UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 24
  · exact hroot.hOcc 26
  · exact hroot.hOcc 30
  · change (∑ j, (-1 : Int) * x j) ≤ -plane339UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
