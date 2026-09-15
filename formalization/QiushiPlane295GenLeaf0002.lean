import QiushiPlane295GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane295GenLeaf0002Refs : Fin 22 → RowRef 46 24 := ![.occ 7, .occ 8, .occ 11, .occ 12, .occ 16, .occ 20, .occ 21, .occ 22, .occ 23, .occ 26, .occ 29, .occ 33, .occ 35, .occ 36, .occ 39, .occ 41, .occ 42, .occ 43, .occ 44, .occ 45, .sumGe, .branchGe 2 (1)]

def plane295GenLeaf0002Mult : Fin 22 → Nat := ![11, 3, 4, 4, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 1, 6, 2, 3, 3, 2, 11, 14]

theorem plane295GenLeaf0002 (x : Fin 24 → Int)
    (hroot : plane295GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane295GenLeaf0002Refs i).resolveCoeff plane295GenOccSys j)
    (fun i => (plane295GenLeaf0002Refs i).resolveRhs plane295GenOccSys) plane295GenLeaf0002Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane295GenLeaf0002Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 7
  · exact hroot.hOcc 8
  · exact hroot.hOcc 11
  · exact hroot.hOcc 12
  · exact hroot.hOcc 16
  · exact hroot.hOcc 20
  · exact hroot.hOcc 21
  · exact hroot.hOcc 22
  · exact hroot.hOcc 23
  · exact hroot.hOcc 26
  · exact hroot.hOcc 29
  · exact hroot.hOcc 33
  · exact hroot.hOcc 35
  · exact hroot.hOcc 36
  · exact hroot.hOcc 39
  · exact hroot.hOcc 41
  · exact hroot.hOcc 42
  · exact hroot.hOcc 43
  · exact hroot.hOcc 44
  · exact hroot.hOcc 45
  · change (∑ j, (-1 : Int) * x j) ≤ -plane295GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 24) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2

end QiushiMatmul
