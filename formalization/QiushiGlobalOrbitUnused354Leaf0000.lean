import QiushiGlobalOrbitUnused354Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane354UnusedGenLeaf0000Refs : Fin 20 → RowRef 30 20 := ![.occ 0, .occ 3, .occ 5, .occ 9, .occ 15, .occ 16, .occ 17, .occ 18, .occ 19, .occ 20, .occ 21, .occ 22, .occ 23, .occ 24, .occ 25, .occ 26, .occ 27, .occ 28, .occ 29, .sumGe]

def plane354UnusedGenLeaf0000Mult : Fin 20 → Nat := ![10, 11, 11, 6, 9, 10, 2, 9, 9, 2, 5, 9, 5, 16, 2, 1, 3, 2, 5, 21]

theorem plane354UnusedGenLeaf0000 (x : Fin 20 → Int)
    (hroot : plane354UnusedGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane354UnusedGenLeaf0000Refs i).resolveCoeff plane354UnusedGenOccSys j)
    (fun i => (plane354UnusedGenLeaf0000Refs i).resolveRhs plane354UnusedGenOccSys) plane354UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane354UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 3
  · exact hroot.hOcc 5
  · exact hroot.hOcc 9
  · exact hroot.hOcc 15
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
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · exact hroot.hOcc 29
  · change (∑ j, (-1 : Int) * x j) ≤ -plane354UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
