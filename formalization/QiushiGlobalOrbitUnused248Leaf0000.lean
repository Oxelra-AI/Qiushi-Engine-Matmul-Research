import QiushiGlobalOrbitUnused248Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane248UnusedGenLeaf0000Refs : Fin 21 → RowRef 23 28 := ![.occ 3, .occ 4, .occ 5, .occ 6, .occ 7, .occ 8, .occ 9, .occ 10, .occ 11, .occ 12, .occ 13, .occ 14, .occ 15, .occ 16, .occ 17, .occ 18, .occ 19, .occ 20, .occ 21, .occ 22, .sumGe]

def plane248UnusedGenLeaf0000Mult : Fin 21 → Nat := ![2, 2, 2, 2, 3, 1, 3, 3, 3, 3, 3, 3, 1, 1, 1, 1, 1, 1, 1, 1, 4]

theorem plane248UnusedGenLeaf0000 (x : Fin 28 → Int)
    (hroot : plane248UnusedGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane248UnusedGenLeaf0000Refs i).resolveCoeff plane248UnusedGenOccSys j)
    (fun i => (plane248UnusedGenLeaf0000Refs i).resolveRhs plane248UnusedGenOccSys) plane248UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane248UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 3
  · exact hroot.hOcc 4
  · exact hroot.hOcc 5
  · exact hroot.hOcc 6
  · exact hroot.hOcc 7
  · exact hroot.hOcc 8
  · exact hroot.hOcc 9
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
  · change (∑ j, (-1 : Int) * x j) ≤ -plane248UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
