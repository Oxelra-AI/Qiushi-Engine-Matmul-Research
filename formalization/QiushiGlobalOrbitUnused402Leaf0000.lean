import QiushiGlobalOrbitUnused402Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane402UnusedGenLeaf0000Refs : Fin 13 → RowRef 31 13 := ![.occ 3, .occ 19, .occ 20, .occ 21, .occ 23, .occ 24, .occ 25, .occ 26, .occ 27, .occ 28, .occ 29, .occ 30, .sumGe]

def plane402UnusedGenLeaf0000Mult : Fin 13 → Nat := ![2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4]

theorem plane402UnusedGenLeaf0000 (x : Fin 13 → Int)
    (hroot : plane402UnusedGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane402UnusedGenLeaf0000Refs i).resolveCoeff plane402UnusedGenOccSys j)
    (fun i => (plane402UnusedGenLeaf0000Refs i).resolveRhs plane402UnusedGenOccSys) plane402UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane402UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 3
  · exact hroot.hOcc 19
  · exact hroot.hOcc 20
  · exact hroot.hOcc 21
  · exact hroot.hOcc 23
  · exact hroot.hOcc 24
  · exact hroot.hOcc 25
  · exact hroot.hOcc 26
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · exact hroot.hOcc 29
  · exact hroot.hOcc 30
  · change (∑ j, (-1 : Int) * x j) ≤ -plane402UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
