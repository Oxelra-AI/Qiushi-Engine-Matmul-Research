import QiushiGlobalOrbitUnused408Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane408UnusedGenLeaf0000Refs : Fin 13 → RowRef 25 18 := ![.occ 13, .occ 14, .occ 15, .occ 16, .occ 17, .occ 18, .occ 19, .occ 20, .occ 21, .occ 22, .occ 23, .occ 24, .sumGe]

def plane408UnusedGenLeaf0000Mult : Fin 13 → Nat := ![2, 2, 2, 3, 2, 2, 1, 1, 2, 1, 2, 1, 5]

theorem plane408UnusedGenLeaf0000 (x : Fin 18 → Int)
    (hroot : plane408UnusedGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane408UnusedGenLeaf0000Refs i).resolveCoeff plane408UnusedGenOccSys j)
    (fun i => (plane408UnusedGenLeaf0000Refs i).resolveRhs plane408UnusedGenOccSys) plane408UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane408UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
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
  · change (∑ j, (-1 : Int) * x j) ≤ -plane408UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
