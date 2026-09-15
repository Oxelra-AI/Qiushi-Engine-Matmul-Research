import QiushiGlobalOrbitUnused306Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane306UnusedGenLeaf0000Refs : Fin 17 → RowRef 30 17 := ![.occ 0, .occ 3, .occ 5, .occ 6, .occ 18, .occ 19, .occ 20, .occ 21, .occ 22, .occ 23, .occ 24, .occ 25, .occ 26, .occ 27, .occ 28, .occ 29, .sumGe]

def plane306UnusedGenLeaf0000Mult : Fin 17 → Nat := ![2, 1, 2, 1, 2, 2, 3, 3, 1, 1, 1, 1, 2, 1, 1, 1, 4]

theorem plane306UnusedGenLeaf0000 (x : Fin 17 → Int)
    (hroot : plane306UnusedGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane306UnusedGenLeaf0000Refs i).resolveCoeff plane306UnusedGenOccSys j)
    (fun i => (plane306UnusedGenLeaf0000Refs i).resolveRhs plane306UnusedGenOccSys) plane306UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane306UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 3
  · exact hroot.hOcc 5
  · exact hroot.hOcc 6
  · exact hroot.hOcc 18
  · exact hroot.hOcc 19
  · exact hroot.hOcc 20
  · exact hroot.hOcc 21
  · exact hroot.hOcc 22
  · exact hroot.hOcc 23
  · exact hroot.hOcc 24
  · exact hroot.hOcc 25
  · exact hroot.hOcc 26
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · exact hroot.hOcc 29
  · change (∑ j, (-1 : Int) * x j) ≤ -plane306UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
