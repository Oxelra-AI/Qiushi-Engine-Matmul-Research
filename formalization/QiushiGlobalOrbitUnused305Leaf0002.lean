import QiushiGlobalOrbitUnused305Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane305UnusedGenLeaf0002Refs : Fin 28 → RowRef 84 30 := ![.occ 0, .occ 5, .occ 8, .occ 9, .occ 13, .occ 14, .occ 16, .occ 26, .occ 34, .occ 35, .occ 38, .occ 42, .occ 47, .occ 59, .occ 61, .occ 64, .occ 69, .occ 71, .occ 76, .occ 78, .occ 79, .occ 81, .occ 83, .sumGe, .nonneg 1, .branchLe 2 (0), .branchGe 7 (1), .branchLe 14 (0)]

def plane305UnusedGenLeaf0002Mult : Fin 28 → Nat := ![8, 9, 1, 3, 1, 2, 3, 3, 4, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 1, 9, 6, 6, 12, 6]

theorem plane305UnusedGenLeaf0002 (x : Fin 30 → Int)
    (hroot : plane305UnusedGenOccSys.RootHolds x)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane305UnusedGenLeaf0002Refs i).resolveCoeff plane305UnusedGenOccSys j)
    (fun i => (plane305UnusedGenLeaf0002Refs i).resolveRhs plane305UnusedGenOccSys) plane305UnusedGenLeaf0002Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane305UnusedGenLeaf0002Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 5
  · exact hroot.hOcc 8
  · exact hroot.hOcc 9
  · exact hroot.hOcc 13
  · exact hroot.hOcc 14
  · exact hroot.hOcc 16
  · exact hroot.hOcc 26
  · exact hroot.hOcc 34
  · exact hroot.hOcc 35
  · exact hroot.hOcc 38
  · exact hroot.hOcc 42
  · exact hroot.hOcc 47
  · exact hroot.hOcc 59
  · exact hroot.hOcc 61
  · exact hroot.hOcc 64
  · exact hroot.hOcc 69
  · exact hroot.hOcc 71
  · exact hroot.hOcc 76
  · exact hroot.hOcc 78
  · exact hroot.hOcc 79
  · exact hroot.hOcc 81
  · exact hroot.hOcc 83
  · change (∑ j, (-1 : Int) * x j) ≤ -plane305UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (1 : Fin 30) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (2 : Fin 30) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (7 : Fin 30) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (14 : Fin 30) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14

end QiushiMatmul
