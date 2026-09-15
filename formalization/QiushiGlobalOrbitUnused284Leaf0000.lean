import QiushiGlobalOrbitUnused284Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane284UnusedGenLeaf0000Refs : Fin 2 → RowRef 34 2 := ![.occ 29, .sumGe]

def plane284UnusedGenLeaf0000Mult : Fin 2 → Nat := ![1, 1]

theorem plane284UnusedGenLeaf0000 (x : Fin 2 → Int)
    (hroot : plane284UnusedGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane284UnusedGenLeaf0000Refs i).resolveCoeff plane284UnusedGenOccSys j)
    (fun i => (plane284UnusedGenLeaf0000Refs i).resolveRhs plane284UnusedGenOccSys) plane284UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane284UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 29
  · change (∑ j, (-1 : Int) * x j) ≤ -plane284UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
