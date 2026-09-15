import QiushiGlobalOrbitUnused371Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane371UnusedGenLeaf0001Refs : Fin 19 → RowRef 38 18 := ![.occ 3, .occ 4, .occ 18, .occ 20, .occ 22, .occ 23, .occ 24, .occ 25, .occ 26, .occ 27, .occ 28, .occ 29, .occ 31, .occ 32, .occ 33, .occ 34, .occ 36, .sumGe, .branchGe 0 (2)]

def plane371UnusedGenLeaf0001Mult : Fin 19 → Nat := ![10, 15, 6, 2, 1, 7, 12, 10, 4, 8, 9, 2, 14, 1, 4, 3, 1, 19, 14]

theorem plane371UnusedGenLeaf0001 (x : Fin 18 → Int)
    (hroot : plane371UnusedGenOccSys.RootHolds x)
    (hLB_0 : (2 : Int) ≤ x 0)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane371UnusedGenLeaf0001Refs i).resolveCoeff plane371UnusedGenOccSys j)
    (fun i => (plane371UnusedGenLeaf0001Refs i).resolveRhs plane371UnusedGenOccSys) plane371UnusedGenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane371UnusedGenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 3
  · exact hroot.hOcc 4
  · exact hroot.hOcc 18
  · exact hroot.hOcc 20
  · exact hroot.hOcc 22
  · exact hroot.hOcc 23
  · exact hroot.hOcc 24
  · exact hroot.hOcc 25
  · exact hroot.hOcc 26
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · exact hroot.hOcc 29
  · exact hroot.hOcc 31
  · exact hroot.hOcc 32
  · exact hroot.hOcc 33
  · exact hroot.hOcc 34
  · exact hroot.hOcc 36
  · change (∑ j, (-1 : Int) * x j) ≤ -plane371UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 18) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
