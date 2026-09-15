import QiushiGlobalOrbitUnused386Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane386UnusedGenLeaf0000Refs : Fin 9 → RowRef 21 19 := ![.occ 13, .occ 14, .occ 15, .occ 16, .occ 17, .occ 18, .occ 19, .occ 20, .sumGe]

def plane386UnusedGenLeaf0000Mult : Fin 9 → Nat := ![2, 2, 2, 2, 1, 1, 1, 1, 4]

theorem plane386UnusedGenLeaf0000 (x : Fin 19 → Int)
    (hroot : plane386UnusedGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane386UnusedGenLeaf0000Refs i).resolveCoeff plane386UnusedGenOccSys j)
    (fun i => (plane386UnusedGenLeaf0000Refs i).resolveRhs plane386UnusedGenOccSys) plane386UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane386UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 13
  · exact hroot.hOcc 14
  · exact hroot.hOcc 15
  · exact hroot.hOcc 16
  · exact hroot.hOcc 17
  · exact hroot.hOcc 18
  · exact hroot.hOcc 19
  · exact hroot.hOcc 20
  · change (∑ j, (-1 : Int) * x j) ≤ -plane386UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
