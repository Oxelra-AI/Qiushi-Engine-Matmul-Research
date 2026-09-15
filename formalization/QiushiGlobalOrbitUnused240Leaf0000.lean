import QiushiGlobalOrbitUnused240Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane240UnusedGenLeaf0000Refs : Fin 10 → RowRef 15 9 := ![.occ 0, .occ 7, .occ 8, .occ 9, .occ 10, .occ 11, .occ 12, .occ 13, .occ 14, .sumGe]

def plane240UnusedGenLeaf0000Mult : Fin 10 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem plane240UnusedGenLeaf0000 (x : Fin 9 → Int)
    (hroot : plane240UnusedGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane240UnusedGenLeaf0000Refs i).resolveCoeff plane240UnusedGenOccSys j)
    (fun i => (plane240UnusedGenLeaf0000Refs i).resolveRhs plane240UnusedGenOccSys) plane240UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane240UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 7
  · exact hroot.hOcc 8
  · exact hroot.hOcc 9
  · exact hroot.hOcc 10
  · exact hroot.hOcc 11
  · exact hroot.hOcc 12
  · exact hroot.hOcc 13
  · exact hroot.hOcc 14
  · change (∑ j, (-1 : Int) * x j) ≤ -plane240UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
