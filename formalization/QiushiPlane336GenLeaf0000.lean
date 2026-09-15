import QiushiPlane336GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane336GenLeaf0000Refs : Fin 13 → RowRef 34 18 := ![.occ 14, .occ 18, .occ 19, .occ 21, .occ 22, .occ 23, .occ 24, .occ 25, .occ 30, .occ 32, .occ 33, .sumGe, .branchLe 1 (1)]

def plane336GenLeaf0000Mult : Fin 13 → Nat := ![5, 3, 5, 1, 2, 5, 2, 3, 1, 4, 4, 9, 9]

theorem plane336GenLeaf0000 (x : Fin 18 → Int)
    (hroot : plane336GenOccSys.RootHolds x)
    (hUB_1 : x 1 ≤ (1 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane336GenLeaf0000Refs i).resolveCoeff plane336GenOccSys j)
    (fun i => (plane336GenLeaf0000Refs i).resolveRhs plane336GenOccSys) plane336GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane336GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 14
  · exact hroot.hOcc 18
  · exact hroot.hOcc 19
  · exact hroot.hOcc 21
  · exact hroot.hOcc 22
  · exact hroot.hOcc 23
  · exact hroot.hOcc 24
  · exact hroot.hOcc 25
  · exact hroot.hOcc 30
  · exact hroot.hOcc 32
  · exact hroot.hOcc 33
  · change (∑ j, (-1 : Int) * x j) ≤ -plane336GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (1 : Fin 18) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_1

end QiushiMatmul
