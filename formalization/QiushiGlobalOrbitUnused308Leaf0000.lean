import QiushiGlobalOrbitUnused308Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane308UnusedGenLeaf0000Refs : Fin 10 → RowRef 28 14 := ![.occ 19, .occ 20, .occ 21, .occ 22, .occ 23, .occ 24, .occ 25, .occ 26, .occ 27, .sumGe]

def plane308UnusedGenLeaf0000Mult : Fin 10 → Nat := ![2, 1, 1, 1, 1, 2, 2, 1, 1, 4]

theorem plane308UnusedGenLeaf0000 (x : Fin 14 → Int)
    (hroot : plane308UnusedGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane308UnusedGenLeaf0000Refs i).resolveCoeff plane308UnusedGenOccSys j)
    (fun i => (plane308UnusedGenLeaf0000Refs i).resolveRhs plane308UnusedGenOccSys) plane308UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane308UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 19
  · exact hroot.hOcc 20
  · exact hroot.hOcc 21
  · exact hroot.hOcc 22
  · exact hroot.hOcc 23
  · exact hroot.hOcc 24
  · exact hroot.hOcc 25
  · exact hroot.hOcc 26
  · exact hroot.hOcc 27
  · change (∑ j, (-1 : Int) * x j) ≤ -plane308UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
