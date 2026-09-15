import QiushiGlobalOrbitUnused379Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane379UnusedGenLeaf0000Refs : Fin 8 → RowRef 22 16 := ![.occ 15, .occ 16, .occ 17, .occ 18, .occ 19, .occ 20, .occ 21, .sumGe]

def plane379UnusedGenLeaf0000Mult : Fin 8 → Nat := ![1, 1, 2, 1, 1, 1, 1, 2]

theorem plane379UnusedGenLeaf0000 (x : Fin 16 → Int)
    (hroot : plane379UnusedGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane379UnusedGenLeaf0000Refs i).resolveCoeff plane379UnusedGenOccSys j)
    (fun i => (plane379UnusedGenLeaf0000Refs i).resolveRhs plane379UnusedGenOccSys) plane379UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane379UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 15
  · exact hroot.hOcc 16
  · exact hroot.hOcc 17
  · exact hroot.hOcc 18
  · exact hroot.hOcc 19
  · exact hroot.hOcc 20
  · exact hroot.hOcc 21
  · change (∑ j, (-1 : Int) * x j) ≤ -plane379UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
