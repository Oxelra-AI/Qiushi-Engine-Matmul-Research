import QiushiGlobalOrbitUnused387Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane387UnusedGenLeaf0000Refs : Fin 13 → RowRef 32 14 := ![.occ 1, .occ 2, .occ 20, .occ 21, .occ 24, .occ 25, .occ 26, .occ 27, .occ 28, .occ 29, .occ 30, .occ 31, .sumGe]

def plane387UnusedGenLeaf0000Mult : Fin 13 → Nat := ![2, 4, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4]

theorem plane387UnusedGenLeaf0000 (x : Fin 14 → Int)
    (hroot : plane387UnusedGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane387UnusedGenLeaf0000Refs i).resolveCoeff plane387UnusedGenOccSys j)
    (fun i => (plane387UnusedGenLeaf0000Refs i).resolveRhs plane387UnusedGenOccSys) plane387UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane387UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · exact hroot.hOcc 2
  · exact hroot.hOcc 20
  · exact hroot.hOcc 21
  · exact hroot.hOcc 24
  · exact hroot.hOcc 25
  · exact hroot.hOcc 26
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · exact hroot.hOcc 29
  · exact hroot.hOcc 30
  · exact hroot.hOcc 31
  · change (∑ j, (-1 : Int) * x j) ≤ -plane387UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
