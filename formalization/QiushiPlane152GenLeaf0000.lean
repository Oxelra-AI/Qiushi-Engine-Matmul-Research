import QiushiPlane152GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane152GenLeaf0000Refs : Fin 10 → RowRef 16 10 := ![.occ 6, .occ 7, .occ 8, .occ 9, .occ 10, .occ 11, .occ 14, .occ 15, .sumGe, .branchLe 0 (1)]

def plane152GenLeaf0000Mult : Fin 10 → Nat := ![2, 2, 2, 2, 1, 1, 1, 1, 4, 4]

theorem plane152GenLeaf0000 (x : Fin 10 → Int)
    (hroot : plane152GenOccSys.RootHolds x)
    (hUB_0 : x 0 ≤ (1 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane152GenLeaf0000Refs i).resolveCoeff plane152GenOccSys j)
    (fun i => (plane152GenLeaf0000Refs i).resolveRhs plane152GenOccSys) plane152GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane152GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 6
  · exact hroot.hOcc 7
  · exact hroot.hOcc 8
  · exact hroot.hOcc 9
  · exact hroot.hOcc 10
  · exact hroot.hOcc 11
  · exact hroot.hOcc 14
  · exact hroot.hOcc 15
  · change (∑ j, (-1 : Int) * x j) ≤ -plane152GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 10) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_0

end QiushiMatmul
