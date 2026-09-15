import QiushiGlobalOrbitUnused289Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane289UnusedGenLeaf0000Refs : Fin 14 → RowRef 27 19 := ![.occ 0, .occ 13, .occ 16, .occ 17, .occ 18, .occ 19, .occ 20, .occ 21, .occ 22, .occ 23, .occ 24, .occ 25, .occ 26, .sumGe]

def plane289UnusedGenLeaf0000Mult : Fin 14 → Nat := ![4, 2, 1, 2, 5, 2, 1, 7, 4, 3, 1, 1, 1, 8]

theorem plane289UnusedGenLeaf0000 (x : Fin 19 → Int)
    (hroot : plane289UnusedGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane289UnusedGenLeaf0000Refs i).resolveCoeff plane289UnusedGenOccSys j)
    (fun i => (plane289UnusedGenLeaf0000Refs i).resolveRhs plane289UnusedGenOccSys) plane289UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane289UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 13
  · exact hroot.hOcc 16
  · exact hroot.hOcc 17
  · exact hroot.hOcc 18
  · exact hroot.hOcc 19
  · exact hroot.hOcc 20
  · exact hroot.hOcc 21
  · exact hroot.hOcc 22
  · exact hroot.hOcc 23
  · exact hroot.hOcc 24
  · exact hroot.hOcc 25
  · exact hroot.hOcc 26
  · change (∑ j, (-1 : Int) * x j) ≤ -plane289UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
