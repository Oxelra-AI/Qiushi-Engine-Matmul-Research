import QiushiGlobalOrbitUnused382Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane382UnusedGenLeaf0000Refs : Fin 5 → RowRef 23 12 := ![.occ 1, .occ 20, .occ 21, .occ 22, .sumGe]

def plane382UnusedGenLeaf0000Mult : Fin 5 → Nat := ![1, 1, 1, 1, 1]

theorem plane382UnusedGenLeaf0000 (x : Fin 12 → Int)
    (hroot : plane382UnusedGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane382UnusedGenLeaf0000Refs i).resolveCoeff plane382UnusedGenOccSys j)
    (fun i => (plane382UnusedGenLeaf0000Refs i).resolveRhs plane382UnusedGenOccSys) plane382UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane382UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · exact hroot.hOcc 20
  · exact hroot.hOcc 21
  · exact hroot.hOcc 22
  · change (∑ j, (-1 : Int) * x j) ≤ -plane382UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
