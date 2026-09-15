import QiushiPlane267GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane267GenLeaf0000Refs : Fin 18 → RowRef 33 20 := ![.occ 11, .occ 13, .occ 14, .occ 15, .occ 17, .occ 18, .occ 19, .occ 20, .occ 21, .occ 23, .occ 24, .occ 27, .occ 28, .occ 29, .occ 30, .occ 32, .sumGe, .branchLe 10 (0)]

def plane267GenLeaf0000Mult : Fin 18 → Nat := ![4, 2, 2, 1, 3, 1, 1, 2, 3, 1, 2, 4, 2, 3, 3, 2, 8, 8]

theorem plane267GenLeaf0000 (x : Fin 20 → Int)
    (hroot : plane267GenOccSys.RootHolds x)
    (hUB_10 : x 10 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane267GenLeaf0000Refs i).resolveCoeff plane267GenOccSys j)
    (fun i => (plane267GenLeaf0000Refs i).resolveRhs plane267GenOccSys) plane267GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane267GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 11
  · exact hroot.hOcc 13
  · exact hroot.hOcc 14
  · exact hroot.hOcc 15
  · exact hroot.hOcc 17
  · exact hroot.hOcc 18
  · exact hroot.hOcc 19
  · exact hroot.hOcc 20
  · exact hroot.hOcc 21
  · exact hroot.hOcc 23
  · exact hroot.hOcc 24
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · exact hroot.hOcc 29
  · exact hroot.hOcc 30
  · exact hroot.hOcc 32
  · change (∑ j, (-1 : Int) * x j) ≤ -plane267GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 20) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10

end QiushiMatmul
