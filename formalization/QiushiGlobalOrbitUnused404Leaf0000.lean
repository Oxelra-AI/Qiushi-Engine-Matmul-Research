import QiushiGlobalOrbitUnused404Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane404UnusedGenLeaf0000Refs : Fin 15 → RowRef 31 14 := ![.occ 16, .occ 17, .occ 19, .occ 20, .occ 21, .occ 22, .occ 23, .occ 24, .occ 25, .occ 26, .occ 27, .occ 28, .occ 29, .occ 30, .sumGe]

def plane404UnusedGenLeaf0000Mult : Fin 15 → Nat := ![16, 12, 4, 12, 6, 6, 14, 7, 11, 7, 1, 10, 2, 10, 30]

theorem plane404UnusedGenLeaf0000 (x : Fin 14 → Int)
    (hroot : plane404UnusedGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane404UnusedGenLeaf0000Refs i).resolveCoeff plane404UnusedGenOccSys j)
    (fun i => (plane404UnusedGenLeaf0000Refs i).resolveRhs plane404UnusedGenOccSys) plane404UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane404UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 16
  · exact hroot.hOcc 17
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
  · exact hroot.hOcc 30
  · change (∑ j, (-1 : Int) * x j) ≤ -plane404UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
