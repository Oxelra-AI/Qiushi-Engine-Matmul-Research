import QiushiGlobalOrbitUnused376Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane376UnusedGenLeaf0000Refs : Fin 6 → RowRef 15 21 := ![.occ 10, .occ 11, .occ 12, .occ 13, .occ 14, .sumGe]

def plane376UnusedGenLeaf0000Mult : Fin 6 → Nat := ![1, 1, 1, 1, 1, 1]

theorem plane376UnusedGenLeaf0000 (x : Fin 21 → Int)
    (hroot : plane376UnusedGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane376UnusedGenLeaf0000Refs i).resolveCoeff plane376UnusedGenOccSys j)
    (fun i => (plane376UnusedGenLeaf0000Refs i).resolveRhs plane376UnusedGenOccSys) plane376UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane376UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 10
  · exact hroot.hOcc 11
  · exact hroot.hOcc 12
  · exact hroot.hOcc 13
  · exact hroot.hOcc 14
  · change (∑ j, (-1 : Int) * x j) ≤ -plane376UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
