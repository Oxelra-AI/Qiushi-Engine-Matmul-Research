import QiushiGlobalOrbitUnused399Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane399UnusedGenLeaf0000Refs : Fin 8 → RowRef 25 17 := ![.occ 13, .occ 14, .occ 15, .occ 16, .occ 17, .occ 19, .occ 24, .sumGe]

def plane399UnusedGenLeaf0000Mult : Fin 8 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1]

theorem plane399UnusedGenLeaf0000 (x : Fin 17 → Int)
    (hroot : plane399UnusedGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane399UnusedGenLeaf0000Refs i).resolveCoeff plane399UnusedGenOccSys j)
    (fun i => (plane399UnusedGenLeaf0000Refs i).resolveRhs plane399UnusedGenOccSys) plane399UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane399UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 13
  · exact hroot.hOcc 14
  · exact hroot.hOcc 15
  · exact hroot.hOcc 16
  · exact hroot.hOcc 17
  · exact hroot.hOcc 19
  · exact hroot.hOcc 24
  · change (∑ j, (-1 : Int) * x j) ≤ -plane399UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
