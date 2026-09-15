import QiushiGlobalOrbitUnused305Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane305UnusedGenLeaf0001Refs : Fin 31 → RowRef 84 30 := ![.occ 0, .occ 8, .occ 11, .occ 16, .occ 27, .occ 30, .occ 31, .occ 35, .occ 36, .occ 37, .occ 41, .occ 43, .occ 45, .occ 49, .occ 50, .occ 52, .occ 58, .occ 60, .occ 63, .occ 69, .occ 74, .occ 75, .occ 78, .occ 79, .occ 81, .occ 82, .sumGe, .nonneg 4, .branchLe 2 (0), .branchLe 7 (0), .branchGe 15 (1)]

def plane305UnusedGenLeaf0001Mult : Fin 31 → Nat := ![313, 88, 43, 269, 19, 84, 35, 95, 15, 13, 4, 62, 21, 34, 34, 2, 25, 32, 48, 22, 66, 69, 44, 130, 51, 48, 313, 73, 189, 262, 276]

theorem plane305UnusedGenLeaf0001 (x : Fin 30 → Int)
    (hroot : plane305UnusedGenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane305UnusedGenLeaf0001Refs i).resolveCoeff plane305UnusedGenOccSys j)
    (fun i => (plane305UnusedGenLeaf0001Refs i).resolveRhs plane305UnusedGenOccSys) plane305UnusedGenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane305UnusedGenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 8
  · exact hroot.hOcc 11
  · exact hroot.hOcc 16
  · exact hroot.hOcc 27
  · exact hroot.hOcc 30
  · exact hroot.hOcc 31
  · exact hroot.hOcc 35
  · exact hroot.hOcc 36
  · exact hroot.hOcc 37
  · exact hroot.hOcc 41
  · exact hroot.hOcc 43
  · exact hroot.hOcc 45
  · exact hroot.hOcc 49
  · exact hroot.hOcc 50
  · exact hroot.hOcc 52
  · exact hroot.hOcc 58
  · exact hroot.hOcc 60
  · exact hroot.hOcc 63
  · exact hroot.hOcc 69
  · exact hroot.hOcc 74
  · exact hroot.hOcc 75
  · exact hroot.hOcc 78
  · exact hroot.hOcc 79
  · exact hroot.hOcc 81
  · exact hroot.hOcc 82
  · change (∑ j, (-1 : Int) * x j) ≤ -plane305UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (4 : Fin 30) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (2 : Fin 30) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (7 : Fin 30) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (15 : Fin 30) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15

end QiushiMatmul
