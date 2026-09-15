import QiushiGlobalOrbitUnused407Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane407UnusedGenLeaf0000Refs : Fin 7 → RowRef 25 12 := ![.occ 19, .occ 20, .occ 21, .occ 22, .occ 23, .occ 24, .sumGe]

def plane407UnusedGenLeaf0000Mult : Fin 7 → Nat := ![1, 1, 1, 1, 1, 1, 2]

theorem plane407UnusedGenLeaf0000 (x : Fin 12 → Int)
    (hroot : plane407UnusedGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane407UnusedGenLeaf0000Refs i).resolveCoeff plane407UnusedGenOccSys j)
    (fun i => (plane407UnusedGenLeaf0000Refs i).resolveRhs plane407UnusedGenOccSys) plane407UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane407UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 19
  · exact hroot.hOcc 20
  · exact hroot.hOcc 21
  · exact hroot.hOcc 22
  · exact hroot.hOcc 23
  · exact hroot.hOcc 24
  · change (∑ j, (-1 : Int) * x j) ≤ -plane407UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
