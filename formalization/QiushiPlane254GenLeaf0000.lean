import QiushiPlane254GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane254GenLeaf0000Refs : Fin 10 → RowRef 26 18 := ![.occ 15, .occ 16, .occ 17, .occ 18, .occ 19, .occ 20, .occ 22, .occ 23, .sumGe, .branchLe 0 (1)]

def plane254GenLeaf0000Mult : Fin 10 → Nat := ![1, 1, 3, 1, 1, 3, 4, 4, 4, 4]

theorem plane254GenLeaf0000 (x : Fin 18 → Int)
    (hroot : plane254GenOccSys.RootHolds x)
    (hUB_0 : x 0 ≤ (1 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane254GenLeaf0000Refs i).resolveCoeff plane254GenOccSys j)
    (fun i => (plane254GenLeaf0000Refs i).resolveRhs plane254GenOccSys) plane254GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane254GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 15
  · exact hroot.hOcc 16
  · exact hroot.hOcc 17
  · exact hroot.hOcc 18
  · exact hroot.hOcc 19
  · exact hroot.hOcc 20
  · exact hroot.hOcc 22
  · exact hroot.hOcc 23
  · change (∑ j, (-1 : Int) * x j) ≤ -plane254GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 18) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_0

end QiushiMatmul
