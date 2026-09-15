import QiushiPlane269GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane269GenLeaf0000Refs : Fin 14 → RowRef 30 21 := ![.occ 14, .occ 15, .occ 17, .occ 18, .occ 19, .occ 20, .occ 22, .occ 23, .occ 24, .occ 27, .occ 28, .sumGe, .branchLe 1 (1), .branchLe 0 (2)]

def plane269GenLeaf0000Mult : Fin 14 → Nat := ![1, 3, 3, 1, 4, 5, 1, 3, 3, 2, 2, 8, 4, 8]

theorem plane269GenLeaf0000 (x : Fin 21 → Int)
    (hroot : plane269GenOccSys.RootHolds x)
    (hUB_1 : x 1 ≤ (1 : Int))
    (hUB_0 : x 0 ≤ (2 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane269GenLeaf0000Refs i).resolveCoeff plane269GenOccSys j)
    (fun i => (plane269GenLeaf0000Refs i).resolveRhs plane269GenOccSys) plane269GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane269GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 14
  · exact hroot.hOcc 15
  · exact hroot.hOcc 17
  · exact hroot.hOcc 18
  · exact hroot.hOcc 19
  · exact hroot.hOcc 20
  · exact hroot.hOcc 22
  · exact hroot.hOcc 23
  · exact hroot.hOcc 24
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · change (∑ j, (-1 : Int) * x j) ≤ -plane269GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (1 : Fin 21) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (0 : Fin 21) then (1 : Int) else 0) * x k) ≤ (2 : Int); simpa only [indicator_sum, one_mul] using hUB_0

end QiushiMatmul
