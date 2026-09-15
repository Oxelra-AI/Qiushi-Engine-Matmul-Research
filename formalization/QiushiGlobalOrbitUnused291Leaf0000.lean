import QiushiGlobalOrbitUnused291Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane291UnusedGenLeaf0000Refs : Fin 4 → RowRef 33 3 := ![.occ 28, .occ 31, .occ 32, .sumGe]

def plane291UnusedGenLeaf0000Mult : Fin 4 → Nat := ![1, 1, 1, 2]

theorem plane291UnusedGenLeaf0000 (x : Fin 3 → Int)
    (hroot : plane291UnusedGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane291UnusedGenLeaf0000Refs i).resolveCoeff plane291UnusedGenOccSys j)
    (fun i => (plane291UnusedGenLeaf0000Refs i).resolveRhs plane291UnusedGenOccSys) plane291UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane291UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 28
  · exact hroot.hOcc 31
  · exact hroot.hOcc 32
  · change (∑ j, (-1 : Int) * x j) ≤ -plane291UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
