import QiushiGlobalOrbitUnused401Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane401UnusedGenLeaf0000Refs : Fin 8 → RowRef 30 9 := ![.occ 3, .occ 4, .occ 24, .occ 25, .occ 27, .occ 28, .occ 29, .sumGe]

def plane401UnusedGenLeaf0000Mult : Fin 8 → Nat := ![1, 1, 1, 1, 1, 1, 1, 2]

theorem plane401UnusedGenLeaf0000 (x : Fin 9 → Int)
    (hroot : plane401UnusedGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane401UnusedGenLeaf0000Refs i).resolveCoeff plane401UnusedGenOccSys j)
    (fun i => (plane401UnusedGenLeaf0000Refs i).resolveRhs plane401UnusedGenOccSys) plane401UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane401UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 3
  · exact hroot.hOcc 4
  · exact hroot.hOcc 24
  · exact hroot.hOcc 25
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · exact hroot.hOcc 29
  · change (∑ j, (-1 : Int) * x j) ≤ -plane401UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
