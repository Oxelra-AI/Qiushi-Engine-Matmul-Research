import QiushiGlobalOrbitUnused92Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane92UnusedGenLeaf0000Refs : Fin 6 → RowRef 11 9 := ![.occ 6, .occ 7, .occ 8, .occ 9, .occ 10, .sumGe]

def plane92UnusedGenLeaf0000Mult : Fin 6 → Nat := ![1, 1, 2, 1, 1, 2]

theorem plane92UnusedGenLeaf0000 (x : Fin 9 → Int)
    (hroot : plane92UnusedGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane92UnusedGenLeaf0000Refs i).resolveCoeff plane92UnusedGenOccSys j)
    (fun i => (plane92UnusedGenLeaf0000Refs i).resolveRhs plane92UnusedGenOccSys) plane92UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane92UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 6
  · exact hroot.hOcc 7
  · exact hroot.hOcc 8
  · exact hroot.hOcc 9
  · exact hroot.hOcc 10
  · change (∑ j, (-1 : Int) * x j) ≤ -plane92UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
