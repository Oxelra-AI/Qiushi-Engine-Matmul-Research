import QiushiPlane276GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane276GenLeaf0001Refs : Fin 10 → RowRef 37 17 := ![.occ 14, .occ 15, .occ 18, .occ 19, .occ 20, .occ 23, .occ 31, .occ 32, .sumGe, .branchGe 2 (2)]

def plane276GenLeaf0001Mult : Fin 10 → Nat := ![3, 1, 1, 1, 3, 3, 1, 3, 4, 8]

theorem plane276GenLeaf0001 (x : Fin 17 → Int)
    (hroot : plane276GenOccSys.RootHolds x)
    (hLB_2 : (2 : Int) ≤ x 2)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane276GenLeaf0001Refs i).resolveCoeff plane276GenOccSys j)
    (fun i => (plane276GenLeaf0001Refs i).resolveRhs plane276GenOccSys) plane276GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane276GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 14
  · exact hroot.hOcc 15
  · exact hroot.hOcc 18
  · exact hroot.hOcc 19
  · exact hroot.hOcc 20
  · exact hroot.hOcc 23
  · exact hroot.hOcc 31
  · exact hroot.hOcc 32
  · change (∑ j, (-1 : Int) * x j) ≤ -plane276GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 17) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2

end QiushiMatmul
