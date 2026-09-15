import QiushiPlane295GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane295GenLeaf0000Refs : Fin 18 → RowRef 46 24 := ![.occ 7, .occ 9, .occ 11, .occ 13, .occ 15, .occ 17, .occ 18, .occ 19, .occ 28, .occ 29, .occ 30, .occ 32, .occ 33, .occ 36, .occ 39, .sumGe, .branchLe 2 (0), .branchLe 4 (0)]

def plane295GenLeaf0000Mult : Fin 18 → Nat := ![3, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2]

theorem plane295GenLeaf0000 (x : Fin 24 → Int)
    (hroot : plane295GenOccSys.RootHolds x)
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane295GenLeaf0000Refs i).resolveCoeff plane295GenOccSys j)
    (fun i => (plane295GenLeaf0000Refs i).resolveRhs plane295GenOccSys) plane295GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane295GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 7
  · exact hroot.hOcc 9
  · exact hroot.hOcc 11
  · exact hroot.hOcc 13
  · exact hroot.hOcc 15
  · exact hroot.hOcc 17
  · exact hroot.hOcc 18
  · exact hroot.hOcc 19
  · exact hroot.hOcc 28
  · exact hroot.hOcc 29
  · exact hroot.hOcc 30
  · exact hroot.hOcc 32
  · exact hroot.hOcc 33
  · exact hroot.hOcc 36
  · exact hroot.hOcc 39
  · change (∑ j, (-1 : Int) * x j) ≤ -plane295GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 24) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (4 : Fin 24) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4

end QiushiMatmul
