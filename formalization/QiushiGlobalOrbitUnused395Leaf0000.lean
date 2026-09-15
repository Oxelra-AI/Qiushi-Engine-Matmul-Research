import QiushiGlobalOrbitUnused395Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane395UnusedGenLeaf0000Refs : Fin 8 → RowRef 28 11 := ![.occ 2, .occ 21, .occ 22, .occ 23, .occ 25, .occ 26, .occ 27, .sumGe]

def plane395UnusedGenLeaf0000Mult : Fin 8 → Nat := ![1, 1, 1, 1, 1, 1, 1, 2]

theorem plane395UnusedGenLeaf0000 (x : Fin 11 → Int)
    (hroot : plane395UnusedGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane395UnusedGenLeaf0000Refs i).resolveCoeff plane395UnusedGenOccSys j)
    (fun i => (plane395UnusedGenLeaf0000Refs i).resolveRhs plane395UnusedGenOccSys) plane395UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane395UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · exact hroot.hOcc 21
  · exact hroot.hOcc 22
  · exact hroot.hOcc 23
  · exact hroot.hOcc 25
  · exact hroot.hOcc 26
  · exact hroot.hOcc 27
  · change (∑ j, (-1 : Int) * x j) ≤ -plane395UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
