import QiushiGlobalOrbitUnused203Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane203UnusedGenLeaf0000Refs : Fin 5 → RowRef 15 4 := ![.occ 11, .occ 12, .occ 13, .occ 14, .sumGe]

def plane203UnusedGenLeaf0000Mult : Fin 5 → Nat := ![2, 1, 1, 1, 3]

theorem plane203UnusedGenLeaf0000 (x : Fin 4 → Int)
    (hroot : plane203UnusedGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane203UnusedGenLeaf0000Refs i).resolveCoeff plane203UnusedGenOccSys j)
    (fun i => (plane203UnusedGenLeaf0000Refs i).resolveRhs plane203UnusedGenOccSys) plane203UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane203UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 11
  · exact hroot.hOcc 12
  · exact hroot.hOcc 13
  · exact hroot.hOcc 14
  · change (∑ j, (-1 : Int) * x j) ≤ -plane203UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
