import QiushiGlobalOrbitUnused389Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane389UnusedGenLeaf0000Refs : Fin 12 → RowRef 35 14 := ![.occ 1, .occ 7, .occ 20, .occ 27, .occ 28, .occ 29, .occ 30, .occ 31, .occ 32, .occ 33, .occ 34, .sumGe]

def plane389UnusedGenLeaf0000Mult : Fin 12 → Nat := ![3, 6, 6, 1, 2, 3, 3, 2, 1, 2, 1, 6]

theorem plane389UnusedGenLeaf0000 (x : Fin 14 → Int)
    (hroot : plane389UnusedGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane389UnusedGenLeaf0000Refs i).resolveCoeff plane389UnusedGenOccSys j)
    (fun i => (plane389UnusedGenLeaf0000Refs i).resolveRhs plane389UnusedGenOccSys) plane389UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane389UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · exact hroot.hOcc 7
  · exact hroot.hOcc 20
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · exact hroot.hOcc 29
  · exact hroot.hOcc 30
  · exact hroot.hOcc 31
  · exact hroot.hOcc 32
  · exact hroot.hOcc 33
  · exact hroot.hOcc 34
  · change (∑ j, (-1 : Int) * x j) ≤ -plane389UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
