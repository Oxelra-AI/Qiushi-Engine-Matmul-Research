import QiushiPlane463LowerGenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane463LowerGenLeaf0000Refs : Fin 5 → RowRef 49 6 := ![.occ 45, .occ 46, .occ 47, .occ 48, .sumGe]

def plane463LowerGenLeaf0000Mult : Fin 5 → Nat := ![1, 1, 1, 1, 2]

theorem plane463LowerGenLeaf0000 (x : Fin 6 → Int)
    (hroot : plane463LowerGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane463LowerGenLeaf0000Refs i).resolveCoeff plane463LowerGenOccSys j)
    (fun i => (plane463LowerGenLeaf0000Refs i).resolveRhs plane463LowerGenOccSys) plane463LowerGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane463LowerGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 45
  · exact hroot.hOcc 46
  · exact hroot.hOcc 47
  · exact hroot.hOcc 48
  · change (∑ j, (-1 : Int) * x j) ≤ -plane463LowerGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
