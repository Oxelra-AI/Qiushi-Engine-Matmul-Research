import QiushiGlobalOrbitUnused301Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane301UnusedGenLeaf0000Refs : Fin 3 → RowRef 20 13 := ![.occ 3, .occ 19, .sumGe]

def plane301UnusedGenLeaf0000Mult : Fin 3 → Nat := ![1, 1, 1]

theorem plane301UnusedGenLeaf0000 (x : Fin 13 → Int)
    (hroot : plane301UnusedGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane301UnusedGenLeaf0000Refs i).resolveCoeff plane301UnusedGenOccSys j)
    (fun i => (plane301UnusedGenLeaf0000Refs i).resolveRhs plane301UnusedGenOccSys) plane301UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane301UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 3
  · exact hroot.hOcc 19
  · change (∑ j, (-1 : Int) * x j) ≤ -plane301UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
