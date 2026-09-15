import QiushiPlane336GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane336GenLeaf0001Refs : Fin 16 → RowRef 34 18 := ![.occ 13, .occ 15, .occ 16, .occ 17, .occ 19, .occ 20, .occ 23, .occ 26, .occ 27, .occ 28, .occ 29, .occ 31, .occ 32, .occ 33, .sumGe, .branchGe 1 (2)]

def plane336GenLeaf0001Mult : Fin 16 → Nat := ![3, 3, 4, 7, 5, 3, 2, 3, 6, 2, 2, 5, 1, 4, 11, 10]

theorem plane336GenLeaf0001 (x : Fin 18 → Int)
    (hroot : plane336GenOccSys.RootHolds x)
    (hLB_1 : (2 : Int) ≤ x 1)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane336GenLeaf0001Refs i).resolveCoeff plane336GenOccSys j)
    (fun i => (plane336GenLeaf0001Refs i).resolveRhs plane336GenOccSys) plane336GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane336GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 13
  · exact hroot.hOcc 15
  · exact hroot.hOcc 16
  · exact hroot.hOcc 17
  · exact hroot.hOcc 19
  · exact hroot.hOcc 20
  · exact hroot.hOcc 23
  · exact hroot.hOcc 26
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · exact hroot.hOcc 29
  · exact hroot.hOcc 31
  · exact hroot.hOcc 32
  · exact hroot.hOcc 33
  · change (∑ j, (-1 : Int) * x j) ≤ -plane336GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (1 : Fin 18) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1

end QiushiMatmul
