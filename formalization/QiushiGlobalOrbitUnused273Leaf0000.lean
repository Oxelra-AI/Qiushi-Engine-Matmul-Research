import QiushiGlobalOrbitUnused273Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane273UnusedGenLeaf0000Refs : Fin 2 → RowRef 44 1 := ![.occ 30, .sumGe]

def plane273UnusedGenLeaf0000Mult : Fin 2 → Nat := ![1, 1]

theorem plane273UnusedGenLeaf0000 (x : Fin 1 → Int)
    (hroot : plane273UnusedGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane273UnusedGenLeaf0000Refs i).resolveCoeff plane273UnusedGenOccSys j)
    (fun i => (plane273UnusedGenLeaf0000Refs i).resolveRhs plane273UnusedGenOccSys) plane273UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane273UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 30
  · change (∑ j, (-1 : Int) * x j) ≤ -plane273UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
