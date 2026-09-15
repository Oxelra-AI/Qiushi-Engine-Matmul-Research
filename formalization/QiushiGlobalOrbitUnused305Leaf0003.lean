import QiushiGlobalOrbitUnused305Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane305UnusedGenLeaf0003Refs : Fin 30 → RowRef 84 30 := ![.occ 0, .occ 5, .occ 12, .occ 16, .occ 22, .occ 23, .occ 24, .occ 25, .occ 26, .occ 29, .occ 34, .occ 37, .occ 39, .occ 57, .occ 62, .occ 65, .occ 70, .occ 71, .occ 75, .occ 78, .occ 79, .occ 80, .occ 81, .occ 83, .sumGe, .nonneg 1, .nonneg 4, .branchLe 2 (0), .branchGe 7 (1), .branchGe 14 (1)]

def plane305UnusedGenLeaf0003Mult : Fin 30 → Nat := ![56, 50, 2, 34, 12, 28, 12, 10, 4, 2, 20, 20, 28, 2, 10, 6, 4, 12, 7, 16, 15, 6, 3, 13, 56, 32, 4, 32, 96, 64]

theorem plane305UnusedGenLeaf0003 (x : Fin 30 → Int)
    (hroot : plane305UnusedGenOccSys.RootHolds x)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hUB_2 : x 2 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane305UnusedGenLeaf0003Refs i).resolveCoeff plane305UnusedGenOccSys j)
    (fun i => (plane305UnusedGenLeaf0003Refs i).resolveRhs plane305UnusedGenOccSys) plane305UnusedGenLeaf0003Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane305UnusedGenLeaf0003Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 5
  · exact hroot.hOcc 12
  · exact hroot.hOcc 16
  · exact hroot.hOcc 22
  · exact hroot.hOcc 23
  · exact hroot.hOcc 24
  · exact hroot.hOcc 25
  · exact hroot.hOcc 26
  · exact hroot.hOcc 29
  · exact hroot.hOcc 34
  · exact hroot.hOcc 37
  · exact hroot.hOcc 39
  · exact hroot.hOcc 57
  · exact hroot.hOcc 62
  · exact hroot.hOcc 65
  · exact hroot.hOcc 70
  · exact hroot.hOcc 71
  · exact hroot.hOcc 75
  · exact hroot.hOcc 78
  · exact hroot.hOcc 79
  · exact hroot.hOcc 80
  · exact hroot.hOcc 81
  · exact hroot.hOcc 83
  · change (∑ j, (-1 : Int) * x j) ≤ -plane305UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (1 : Fin 30) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (4 : Fin 30) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (2 : Fin 30) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (7 : Fin 30) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (14 : Fin 30) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14

end QiushiMatmul
