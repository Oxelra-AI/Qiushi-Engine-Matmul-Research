import QiushiPlane471LowerGenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane471LowerGenLeaf0000Refs : Fin 5 → RowRef 53 6 := ![.occ 49, .occ 50, .occ 51, .occ 52, .sumGe]

def plane471LowerGenLeaf0000Mult : Fin 5 → Nat := ![1, 1, 1, 1, 2]

theorem plane471LowerGenLeaf0000 (x : Fin 6 → Int)
    (hroot : plane471LowerGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane471LowerGenLeaf0000Refs i).resolveCoeff plane471LowerGenOccSys j)
    (fun i => (plane471LowerGenLeaf0000Refs i).resolveRhs plane471LowerGenOccSys) plane471LowerGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane471LowerGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 49
  · exact hroot.hOcc 50
  · exact hroot.hOcc 51
  · exact hroot.hOcc 52
  · change (∑ j, (-1 : Int) * x j) ≤ -plane471LowerGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
