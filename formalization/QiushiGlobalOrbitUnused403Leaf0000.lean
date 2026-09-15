import QiushiGlobalOrbitUnused403Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane403UnusedGenLeaf0000Refs : Fin 4 → RowRef 16 18 := ![.occ 13, .occ 14, .occ 15, .sumGe]

def plane403UnusedGenLeaf0000Mult : Fin 4 → Nat := ![1, 1, 1, 1]

theorem plane403UnusedGenLeaf0000 (x : Fin 18 → Int)
    (hroot : plane403UnusedGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane403UnusedGenLeaf0000Refs i).resolveCoeff plane403UnusedGenOccSys j)
    (fun i => (plane403UnusedGenLeaf0000Refs i).resolveRhs plane403UnusedGenOccSys) plane403UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane403UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 13
  · exact hroot.hOcc 14
  · exact hroot.hOcc 15
  · change (∑ j, (-1 : Int) * x j) ≤ -plane403UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
