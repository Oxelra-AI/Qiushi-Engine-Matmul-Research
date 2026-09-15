import QiushiGlobalOrbitUnused305Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane305UnusedGenLeaf0004Refs : Fin 29 → RowRef 84 30 := ![.occ 0, .occ 2, .occ 5, .occ 6, .occ 7, .occ 8, .occ 10, .occ 11, .occ 12, .occ 16, .occ 21, .occ 34, .occ 54, .occ 57, .occ 61, .occ 64, .occ 71, .occ 72, .occ 75, .occ 76, .occ 78, .occ 79, .occ 80, .occ 81, .occ 82, .sumGe, .branchGe 2 (1), .branchLe 9 (0), .branchLe 13 (0)]

def plane305UnusedGenLeaf0004Mult : Fin 29 → Nat := ![40, 12, 20, 8, 16, 24, 4, 16, 8, 24, 4, 8, 2, 8, 2, 4, 6, 8, 9, 2, 5, 4, 7, 10, 1, 40, 12, 12, 24]

theorem plane305UnusedGenLeaf0004 (x : Fin 30 → Int)
    (hroot : plane305UnusedGenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane305UnusedGenLeaf0004Refs i).resolveCoeff plane305UnusedGenOccSys j)
    (fun i => (plane305UnusedGenLeaf0004Refs i).resolveRhs plane305UnusedGenOccSys) plane305UnusedGenLeaf0004Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane305UnusedGenLeaf0004Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 2
  · exact hroot.hOcc 5
  · exact hroot.hOcc 6
  · exact hroot.hOcc 7
  · exact hroot.hOcc 8
  · exact hroot.hOcc 10
  · exact hroot.hOcc 11
  · exact hroot.hOcc 12
  · exact hroot.hOcc 16
  · exact hroot.hOcc 21
  · exact hroot.hOcc 34
  · exact hroot.hOcc 54
  · exact hroot.hOcc 57
  · exact hroot.hOcc 61
  · exact hroot.hOcc 64
  · exact hroot.hOcc 71
  · exact hroot.hOcc 72
  · exact hroot.hOcc 75
  · exact hroot.hOcc 76
  · exact hroot.hOcc 78
  · exact hroot.hOcc 79
  · exact hroot.hOcc 80
  · exact hroot.hOcc 81
  · exact hroot.hOcc 82
  · change (∑ j, (-1 : Int) * x j) ≤ -plane305UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 30) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (9 : Fin 30) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (13 : Fin 30) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13

end QiushiMatmul
