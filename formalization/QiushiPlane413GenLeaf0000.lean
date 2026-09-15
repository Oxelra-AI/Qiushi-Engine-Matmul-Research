import QiushiPlane413GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane413GenLeaf0000Refs : Fin 9 → RowRef 49 21 := ![.occ 41, .occ 42, .occ 43, .occ 44, .occ 45, .occ 46, .occ 47, .occ 48, .sumGe]

def plane413GenLeaf0000Mult : Fin 9 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 2]

theorem plane413GenLeaf0000 (x : Fin 21 → Int)
    (hroot : plane413GenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane413GenLeaf0000Refs i).resolveCoeff plane413GenOccSys j)
    (fun i => (plane413GenLeaf0000Refs i).resolveRhs plane413GenOccSys) plane413GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane413GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 41
  · exact hroot.hOcc 42
  · exact hroot.hOcc 43
  · exact hroot.hOcc 44
  · exact hroot.hOcc 45
  · exact hroot.hOcc 46
  · exact hroot.hOcc 47
  · exact hroot.hOcc 48
  · change (∑ j, (-1 : Int) * x j) ≤ -plane413GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
