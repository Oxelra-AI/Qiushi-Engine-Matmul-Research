import QiushiGlobalOrbitUnused88Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane88UnusedGenLeaf0000Refs : Fin 2 → RowRef 13 3 := ![.occ 12, .sumGe]

def plane88UnusedGenLeaf0000Mult : Fin 2 → Nat := ![1, 1]

theorem plane88UnusedGenLeaf0000 (x : Fin 3 → Int)
    (hroot : plane88UnusedGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane88UnusedGenLeaf0000Refs i).resolveCoeff plane88UnusedGenOccSys j)
    (fun i => (plane88UnusedGenLeaf0000Refs i).resolveRhs plane88UnusedGenOccSys) plane88UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane88UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 12
  · change (∑ j, (-1 : Int) * x j) ≤ -plane88UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
