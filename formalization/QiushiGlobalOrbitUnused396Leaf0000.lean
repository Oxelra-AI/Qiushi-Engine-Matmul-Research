import QiushiGlobalOrbitUnused396Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane396UnusedGenLeaf0000Refs : Fin 14 → RowRef 32 14 := ![.occ 17, .occ 18, .occ 19, .occ 22, .occ 23, .occ 24, .occ 25, .occ 26, .occ 27, .occ 28, .occ 29, .occ 30, .occ 31, .sumGe]

def plane396UnusedGenLeaf0000Mult : Fin 14 → Nat := ![2, 2, 4, 4, 3, 3, 4, 1, 3, 4, 1, 5, 4, 12]

theorem plane396UnusedGenLeaf0000 (x : Fin 14 → Int)
    (hroot : plane396UnusedGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane396UnusedGenLeaf0000Refs i).resolveCoeff plane396UnusedGenOccSys j)
    (fun i => (plane396UnusedGenLeaf0000Refs i).resolveRhs plane396UnusedGenOccSys) plane396UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane396UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 17
  · exact hroot.hOcc 18
  · exact hroot.hOcc 19
  · exact hroot.hOcc 22
  · exact hroot.hOcc 23
  · exact hroot.hOcc 24
  · exact hroot.hOcc 25
  · exact hroot.hOcc 26
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · exact hroot.hOcc 29
  · exact hroot.hOcc 30
  · exact hroot.hOcc 31
  · change (∑ j, (-1 : Int) * x j) ≤ -plane396UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
