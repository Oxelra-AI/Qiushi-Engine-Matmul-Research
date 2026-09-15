import QiushiGlobalOrbitUnused333Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane333UnusedGenLeaf0000Refs : Fin 8 → RowRef 36 10 := ![.occ 3, .occ 7, .occ 21, .occ 28, .occ 33, .occ 34, .occ 35, .sumGe]

def plane333UnusedGenLeaf0000Mult : Fin 8 → Nat := ![3, 3, 1, 1, 1, 2, 2, 3]

theorem plane333UnusedGenLeaf0000 (x : Fin 10 → Int)
    (hroot : plane333UnusedGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane333UnusedGenLeaf0000Refs i).resolveCoeff plane333UnusedGenOccSys j)
    (fun i => (plane333UnusedGenLeaf0000Refs i).resolveRhs plane333UnusedGenOccSys) plane333UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane333UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 3
  · exact hroot.hOcc 7
  · exact hroot.hOcc 21
  · exact hroot.hOcc 28
  · exact hroot.hOcc 33
  · exact hroot.hOcc 34
  · exact hroot.hOcc 35
  · change (∑ j, (-1 : Int) * x j) ≤ -plane333UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
