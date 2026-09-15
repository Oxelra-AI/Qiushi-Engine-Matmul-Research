import QiushiGlobalOrbitUnused378Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane378UnusedGenLeaf0000Refs : Fin 2 → RowRef 17 15 := ![.occ 16, .sumGe]

def plane378UnusedGenLeaf0000Mult : Fin 2 → Nat := ![1, 1]

theorem plane378UnusedGenLeaf0000 (x : Fin 15 → Int)
    (hroot : plane378UnusedGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane378UnusedGenLeaf0000Refs i).resolveCoeff plane378UnusedGenOccSys j)
    (fun i => (plane378UnusedGenLeaf0000Refs i).resolveRhs plane378UnusedGenOccSys) plane378UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane378UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 16
  · change (∑ j, (-1 : Int) * x j) ≤ -plane378UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
