import QiushiGlobalOrbitUnused406Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane406UnusedGenLeaf0000Refs : Fin 5 → RowRef 18 17 := ![.occ 14, .occ 15, .occ 16, .occ 17, .sumGe]

def plane406UnusedGenLeaf0000Mult : Fin 5 → Nat := ![1, 1, 1, 1, 1]

theorem plane406UnusedGenLeaf0000 (x : Fin 17 → Int)
    (hroot : plane406UnusedGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane406UnusedGenLeaf0000Refs i).resolveCoeff plane406UnusedGenOccSys j)
    (fun i => (plane406UnusedGenLeaf0000Refs i).resolveRhs plane406UnusedGenOccSys) plane406UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane406UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 14
  · exact hroot.hOcc 15
  · exact hroot.hOcc 16
  · exact hroot.hOcc 17
  · change (∑ j, (-1 : Int) * x j) ≤ -plane406UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
