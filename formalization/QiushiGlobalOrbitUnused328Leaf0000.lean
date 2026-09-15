import QiushiGlobalOrbitUnused328Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane328UnusedGenLeaf0000Refs : Fin 5 → RowRef 29 8 := ![.occ 3, .occ 7, .occ 27, .occ 28, .sumGe]

def plane328UnusedGenLeaf0000Mult : Fin 5 → Nat := ![1, 1, 1, 1, 1]

theorem plane328UnusedGenLeaf0000 (x : Fin 8 → Int)
    (hroot : plane328UnusedGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane328UnusedGenLeaf0000Refs i).resolveCoeff plane328UnusedGenOccSys j)
    (fun i => (plane328UnusedGenLeaf0000Refs i).resolveRhs plane328UnusedGenOccSys) plane328UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane328UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 3
  · exact hroot.hOcc 7
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · change (∑ j, (-1 : Int) * x j) ≤ -plane328UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
