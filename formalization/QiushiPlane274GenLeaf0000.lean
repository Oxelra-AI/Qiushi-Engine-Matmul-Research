import QiushiPlane274GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane274GenLeaf0000Refs : Fin 20 → RowRef 29 21 := ![.occ 10, .occ 11, .occ 12, .occ 13, .occ 14, .occ 15, .occ 16, .occ 17, .occ 18, .occ 19, .occ 20, .occ 21, .occ 22, .occ 23, .occ 24, .occ 25, .occ 26, .occ 27, .occ 28, .sumGe]

def plane274GenLeaf0000Mult : Fin 20 → Nat := ![3, 2, 3, 3, 2, 3, 13, 5, 5, 3, 6, 4, 5, 3, 10, 2, 4, 7, 6, 23]

theorem plane274GenLeaf0000 (x : Fin 21 → Int)
    (hroot : plane274GenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane274GenLeaf0000Refs i).resolveCoeff plane274GenOccSys j)
    (fun i => (plane274GenLeaf0000Refs i).resolveRhs plane274GenOccSys) plane274GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane274GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 10
  · exact hroot.hOcc 11
  · exact hroot.hOcc 12
  · exact hroot.hOcc 13
  · exact hroot.hOcc 14
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
  · change (∑ j, (-1 : Int) * x j) ≤ -plane274GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
