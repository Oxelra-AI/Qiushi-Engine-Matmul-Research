import QiushiGlobalOrbitUnused305Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane305UnusedGenLeaf0005Refs : Fin 29 → RowRef 84 30 := ![.occ 0, .occ 4, .occ 5, .occ 11, .occ 16, .occ 17, .occ 18, .occ 20, .occ 39, .occ 40, .occ 43, .occ 47, .occ 55, .occ 56, .occ 57, .occ 58, .occ 64, .occ 66, .occ 68, .occ 69, .occ 78, .occ 79, .occ 81, .occ 82, .occ 83, .sumGe, .branchGe 2 (1), .branchLe 9 (0), .branchGe 13 (1)]

def plane305UnusedGenLeaf0005Mult : Fin 29 → Nat := ![34, 7, 23, 4, 13, 1, 5, 1, 7, 2, 9, 2, 23, 2, 12, 4, 4, 3, 6, 11, 7, 13, 5, 2, 15, 43, 20, 18, 50]

theorem plane305UnusedGenLeaf0005 (x : Fin 30 → Int)
    (hroot : plane305UnusedGenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hUB_9 : x 9 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane305UnusedGenLeaf0005Refs i).resolveCoeff plane305UnusedGenOccSys j)
    (fun i => (plane305UnusedGenLeaf0005Refs i).resolveRhs plane305UnusedGenOccSys) plane305UnusedGenLeaf0005Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane305UnusedGenLeaf0005Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 4
  · exact hroot.hOcc 5
  · exact hroot.hOcc 11
  · exact hroot.hOcc 16
  · exact hroot.hOcc 17
  · exact hroot.hOcc 18
  · exact hroot.hOcc 20
  · exact hroot.hOcc 39
  · exact hroot.hOcc 40
  · exact hroot.hOcc 43
  · exact hroot.hOcc 47
  · exact hroot.hOcc 55
  · exact hroot.hOcc 56
  · exact hroot.hOcc 57
  · exact hroot.hOcc 58
  · exact hroot.hOcc 64
  · exact hroot.hOcc 66
  · exact hroot.hOcc 68
  · exact hroot.hOcc 69
  · exact hroot.hOcc 78
  · exact hroot.hOcc 79
  · exact hroot.hOcc 81
  · exact hroot.hOcc 82
  · exact hroot.hOcc 83
  · change (∑ j, (-1 : Int) * x j) ≤ -plane305UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 30) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (9 : Fin 30) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (13 : Fin 30) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13

end QiushiMatmul
