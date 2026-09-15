import QiushiGlobalOrbitUnused305Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane305UnusedGenLeaf0000Refs : Fin 31 → RowRef 84 30 := ![.occ 0, .occ 8, .occ 11, .occ 12, .occ 15, .occ 16, .occ 32, .occ 33, .occ 41, .occ 42, .occ 43, .occ 44, .occ 45, .occ 46, .occ 48, .occ 51, .occ 67, .occ 72, .occ 73, .occ 74, .occ 75, .occ 77, .occ 78, .occ 79, .occ 80, .occ 82, .occ 83, .sumGe, .branchLe 2 (0), .branchLe 7 (0), .branchLe 15 (0)]

def plane305UnusedGenLeaf0000Mult : Fin 31 → Nat := ![100, 16, 8, 4, 12, 32, 4, 28, 30, 6, 14, 2, 16, 4, 18, 32, 10, 20, 8, 22, 30, 1, 33, 22, 13, 20, 13, 118, 72, 104, 64]

theorem plane305UnusedGenLeaf0000 (x : Fin 30 → Int)
    (hroot : plane305UnusedGenOccSys.RootHolds x)
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane305UnusedGenLeaf0000Refs i).resolveCoeff plane305UnusedGenOccSys j)
    (fun i => (plane305UnusedGenLeaf0000Refs i).resolveRhs plane305UnusedGenOccSys) plane305UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane305UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 8
  · exact hroot.hOcc 11
  · exact hroot.hOcc 12
  · exact hroot.hOcc 15
  · exact hroot.hOcc 16
  · exact hroot.hOcc 32
  · exact hroot.hOcc 33
  · exact hroot.hOcc 41
  · exact hroot.hOcc 42
  · exact hroot.hOcc 43
  · exact hroot.hOcc 44
  · exact hroot.hOcc 45
  · exact hroot.hOcc 46
  · exact hroot.hOcc 48
  · exact hroot.hOcc 51
  · exact hroot.hOcc 67
  · exact hroot.hOcc 72
  · exact hroot.hOcc 73
  · exact hroot.hOcc 74
  · exact hroot.hOcc 75
  · exact hroot.hOcc 77
  · exact hroot.hOcc 78
  · exact hroot.hOcc 79
  · exact hroot.hOcc 80
  · exact hroot.hOcc 82
  · exact hroot.hOcc 83
  · change (∑ j, (-1 : Int) * x j) ≤ -plane305UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 30) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (7 : Fin 30) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (15 : Fin 30) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15

end QiushiMatmul
