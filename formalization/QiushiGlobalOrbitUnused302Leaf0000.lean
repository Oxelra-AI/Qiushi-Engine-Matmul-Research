import QiushiGlobalOrbitUnused302Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane302UnusedGenLeaf0000Refs : Fin 4 → RowRef 25 9 := ![.occ 22, .occ 23, .occ 24, .sumGe]

def plane302UnusedGenLeaf0000Mult : Fin 4 → Nat := ![1, 1, 1, 1]

theorem plane302UnusedGenLeaf0000 (x : Fin 9 → Int)
    (hroot : plane302UnusedGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane302UnusedGenLeaf0000Refs i).resolveCoeff plane302UnusedGenOccSys j)
    (fun i => (plane302UnusedGenLeaf0000Refs i).resolveRhs plane302UnusedGenOccSys) plane302UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane302UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 22
  · exact hroot.hOcc 23
  · exact hroot.hOcc 24
  · change (∑ j, (-1 : Int) * x j) ≤ -plane302UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
