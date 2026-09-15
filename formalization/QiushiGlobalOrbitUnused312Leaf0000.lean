import QiushiGlobalOrbitUnused312Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane312UnusedGenLeaf0000Refs : Fin 7 → RowRef 20 17 := ![.occ 14, .occ 15, .occ 16, .occ 17, .occ 18, .occ 19, .sumGe]

def plane312UnusedGenLeaf0000Mult : Fin 7 → Nat := ![1, 1, 1, 1, 1, 1, 1]

theorem plane312UnusedGenLeaf0000 (x : Fin 17 → Int)
    (hroot : plane312UnusedGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane312UnusedGenLeaf0000Refs i).resolveCoeff plane312UnusedGenOccSys j)
    (fun i => (plane312UnusedGenLeaf0000Refs i).resolveRhs plane312UnusedGenOccSys) plane312UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane312UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 14
  · exact hroot.hOcc 15
  · exact hroot.hOcc 16
  · exact hroot.hOcc 17
  · exact hroot.hOcc 18
  · exact hroot.hOcc 19
  · change (∑ j, (-1 : Int) * x j) ≤ -plane312UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
