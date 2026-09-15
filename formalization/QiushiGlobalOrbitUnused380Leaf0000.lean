import QiushiGlobalOrbitUnused380Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane380UnusedGenLeaf0000Refs : Fin 6 → RowRef 26 10 := ![.occ 3, .occ 22, .occ 23, .occ 24, .occ 25, .sumGe]

def plane380UnusedGenLeaf0000Mult : Fin 6 → Nat := ![1, 1, 1, 1, 1, 1]

theorem plane380UnusedGenLeaf0000 (x : Fin 10 → Int)
    (hroot : plane380UnusedGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane380UnusedGenLeaf0000Refs i).resolveCoeff plane380UnusedGenOccSys j)
    (fun i => (plane380UnusedGenLeaf0000Refs i).resolveRhs plane380UnusedGenOccSys) plane380UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane380UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 3
  · exact hroot.hOcc 22
  · exact hroot.hOcc 23
  · exact hroot.hOcc 24
  · exact hroot.hOcc 25
  · change (∑ j, (-1 : Int) * x j) ≤ -plane380UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
