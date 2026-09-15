import QiushiPlane295GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane295GenLeaf0001Refs : Fin 25 → RowRef 46 24 := ![.occ 7, .occ 8, .occ 9, .occ 10, .occ 12, .occ 14, .occ 16, .occ 23, .occ 24, .occ 25, .occ 26, .occ 27, .occ 28, .occ 31, .occ 32, .occ 33, .occ 34, .occ 36, .occ 37, .occ 38, .occ 39, .occ 40, .sumGe, .branchLe 2 (0), .branchGe 4 (1)]

def plane295GenLeaf0001Mult : Fin 25 → Nat := ![40, 10, 14, 6, 10, 2, 12, 1, 8, 19, 12, 16, 16, 8, 7, 11, 2, 13, 11, 2, 13, 1, 40, 40, 42]

theorem plane295GenLeaf0001 (x : Fin 24 → Int)
    (hroot : plane295GenOccSys.RootHolds x)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_2 : x 2 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane295GenLeaf0001Refs i).resolveCoeff plane295GenOccSys j)
    (fun i => (plane295GenLeaf0001Refs i).resolveRhs plane295GenOccSys) plane295GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane295GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 7
  · exact hroot.hOcc 8
  · exact hroot.hOcc 9
  · exact hroot.hOcc 10
  · exact hroot.hOcc 12
  · exact hroot.hOcc 14
  · exact hroot.hOcc 16
  · exact hroot.hOcc 23
  · exact hroot.hOcc 24
  · exact hroot.hOcc 25
  · exact hroot.hOcc 26
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · exact hroot.hOcc 31
  · exact hroot.hOcc 32
  · exact hroot.hOcc 33
  · exact hroot.hOcc 34
  · exact hroot.hOcc 36
  · exact hroot.hOcc 37
  · exact hroot.hOcc 38
  · exact hroot.hOcc 39
  · exact hroot.hOcc 40
  · change (∑ j, (-1 : Int) * x j) ≤ -plane295GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 24) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (4 : Fin 24) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4

end QiushiMatmul
