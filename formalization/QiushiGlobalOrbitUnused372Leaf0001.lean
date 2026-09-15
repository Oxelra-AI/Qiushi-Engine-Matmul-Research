import QiushiGlobalOrbitUnused372Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane372UnusedGenLeaf0001Refs : Fin 22 → RowRef 37 26 := ![.occ 1, .occ 2, .occ 4, .occ 11, .occ 13, .occ 15, .occ 16, .occ 17, .occ 18, .occ 20, .occ 21, .occ 22, .occ 23, .occ 24, .occ 25, .occ 26, .occ 27, .occ 28, .occ 29, .occ 30, .sumGe, .branchGe 25 (1)]

def plane372UnusedGenLeaf0001Mult : Fin 22 → Nat := ![2, 2, 4, 6, 4, 2, 6, 6, 2, 3, 2, 1, 1, 3, 3, 7, 1, 7, 1, 3, 10, 8]

theorem plane372UnusedGenLeaf0001 (x : Fin 26 → Int)
    (hroot : plane372UnusedGenOccSys.RootHolds x)
    (hLB_25 : (1 : Int) ≤ x 25)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane372UnusedGenLeaf0001Refs i).resolveCoeff plane372UnusedGenOccSys j)
    (fun i => (plane372UnusedGenLeaf0001Refs i).resolveRhs plane372UnusedGenOccSys) plane372UnusedGenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane372UnusedGenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · exact hroot.hOcc 2
  · exact hroot.hOcc 4
  · exact hroot.hOcc 11
  · exact hroot.hOcc 13
  · exact hroot.hOcc 15
  · exact hroot.hOcc 16
  · exact hroot.hOcc 17
  · exact hroot.hOcc 18
  · exact hroot.hOcc 20
  · exact hroot.hOcc 21
  · exact hroot.hOcc 22
  · exact hroot.hOcc 23
  · exact hroot.hOcc 24
  · exact hroot.hOcc 25
  · exact hroot.hOcc 26
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · exact hroot.hOcc 29
  · exact hroot.hOcc 30
  · change (∑ j, (-1 : Int) * x j) ≤ -plane372UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (25 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25

end QiushiMatmul
