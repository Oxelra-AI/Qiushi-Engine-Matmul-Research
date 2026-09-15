import QiushiGlobalOrbitUnused394Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane394UnusedGenLeaf0000Refs : Fin 8 → RowRef 32 9 := ![.occ 2, .occ 3, .occ 13, .occ 25, .occ 26, .occ 30, .occ 31, .sumGe]

def plane394UnusedGenLeaf0000Mult : Fin 8 → Nat := ![1, 1, 1, 1, 1, 1, 1, 2]

theorem plane394UnusedGenLeaf0000 (x : Fin 9 → Int)
    (hroot : plane394UnusedGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane394UnusedGenLeaf0000Refs i).resolveCoeff plane394UnusedGenOccSys j)
    (fun i => (plane394UnusedGenLeaf0000Refs i).resolveRhs plane394UnusedGenOccSys) plane394UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane394UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · exact hroot.hOcc 3
  · exact hroot.hOcc 13
  · exact hroot.hOcc 25
  · exact hroot.hOcc 26
  · exact hroot.hOcc 30
  · exact hroot.hOcc 31
  · change (∑ j, (-1 : Int) * x j) ≤ -plane394UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
