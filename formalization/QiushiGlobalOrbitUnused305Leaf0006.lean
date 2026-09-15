import QiushiGlobalOrbitUnused305Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane305UnusedGenLeaf0006Refs : Fin 31 → RowRef 84 30 := ![.occ 0, .occ 3, .occ 5, .occ 6, .occ 8, .occ 11, .occ 12, .occ 16, .occ 19, .occ 27, .occ 28, .occ 29, .occ 33, .occ 41, .occ 47, .occ 53, .occ 56, .occ 58, .occ 63, .occ 66, .occ 69, .occ 72, .occ 79, .occ 80, .occ 82, .occ 83, .sumGe, .nonneg 7, .nonneg 29, .branchGe 2 (1), .branchGe 9 (1)]

def plane305UnusedGenLeaf0006Mult : Fin 31 → Nat := ![50, 14, 50, 4, 21, 7, 11, 28, 20, 5, 7, 7, 2, 13, 1, 8, 21, 10, 12, 4, 3, 4, 1, 23, 16, 3, 51, 2, 4, 34, 60]

theorem plane305UnusedGenLeaf0006 (x : Fin 30 → Int)
    (hroot : plane305UnusedGenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_9 : (1 : Int) ≤ x 9)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane305UnusedGenLeaf0006Refs i).resolveCoeff plane305UnusedGenOccSys j)
    (fun i => (plane305UnusedGenLeaf0006Refs i).resolveRhs plane305UnusedGenOccSys) plane305UnusedGenLeaf0006Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane305UnusedGenLeaf0006Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 3
  · exact hroot.hOcc 5
  · exact hroot.hOcc 6
  · exact hroot.hOcc 8
  · exact hroot.hOcc 11
  · exact hroot.hOcc 12
  · exact hroot.hOcc 16
  · exact hroot.hOcc 19
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · exact hroot.hOcc 29
  · exact hroot.hOcc 33
  · exact hroot.hOcc 41
  · exact hroot.hOcc 47
  · exact hroot.hOcc 53
  · exact hroot.hOcc 56
  · exact hroot.hOcc 58
  · exact hroot.hOcc 63
  · exact hroot.hOcc 66
  · exact hroot.hOcc 69
  · exact hroot.hOcc 72
  · exact hroot.hOcc 79
  · exact hroot.hOcc 80
  · exact hroot.hOcc 82
  · exact hroot.hOcc 83
  · change (∑ j, (-1 : Int) * x j) ≤ -plane305UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 30) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (29 : Fin 30) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (2 : Fin 30) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (9 : Fin 30) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9

end QiushiMatmul
