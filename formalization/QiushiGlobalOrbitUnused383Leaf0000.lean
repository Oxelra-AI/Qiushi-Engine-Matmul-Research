import QiushiGlobalOrbitUnused383Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane383UnusedGenLeaf0000Refs : Fin 10 → RowRef 28 12 := ![.occ 0, .occ 20, .occ 21, .occ 22, .occ 23, .occ 24, .occ 25, .occ 26, .occ 27, .sumGe]

def plane383UnusedGenLeaf0000Mult : Fin 10 → Nat := ![2, 1, 1, 1, 3, 2, 2, 1, 1, 4]

theorem plane383UnusedGenLeaf0000 (x : Fin 12 → Int)
    (hroot : plane383UnusedGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane383UnusedGenLeaf0000Refs i).resolveCoeff plane383UnusedGenOccSys j)
    (fun i => (plane383UnusedGenLeaf0000Refs i).resolveRhs plane383UnusedGenOccSys) plane383UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane383UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 20
  · exact hroot.hOcc 21
  · exact hroot.hOcc 22
  · exact hroot.hOcc 23
  · exact hroot.hOcc 24
  · exact hroot.hOcc 25
  · exact hroot.hOcc 26
  · exact hroot.hOcc 27
  · change (∑ j, (-1 : Int) * x j) ≤ -plane383UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
