import QiushiPlane452GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane452GenLeaf0000Refs : Fin 34 → RowRef 117 35 := ![.occ 29, .occ 33, .occ 42, .occ 48, .occ 49, .occ 50, .occ 51, .occ 60, .occ 62, .occ 63, .occ 71, .occ 73, .occ 76, .occ 78, .occ 83, .occ 84, .occ 85, .occ 86, .occ 91, .occ 92, .occ 95, .occ 97, .occ 98, .occ 100, .occ 102, .occ 103, .occ 105, .occ 106, .occ 107, .sumGe, .branchLe 8 (0), .branchLe 10 (0), .branchLe 7 (0), .branchLe 0 (0)]

def plane452GenLeaf0000Mult : Fin 34 → Nat := ![2, 1, 3, 3, 3, 3, 1, 4, 1, 3, 3, 3, 4, 1, 5, 5, 5, 5, 3, 3, 4, 4, 6, 4, 3, 3, 6, 4, 5, 10, 10, 10, 10, 10]

theorem plane452GenLeaf0000 (x : Fin 35 → Int)
    (hroot : plane452GenOccSys.RootHolds x)
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_0 : x 0 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane452GenLeaf0000Refs i).resolveCoeff plane452GenOccSys j)
    (fun i => (plane452GenLeaf0000Refs i).resolveRhs plane452GenOccSys) plane452GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane452GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 29
  · exact hroot.hOcc 33
  · exact hroot.hOcc 42
  · exact hroot.hOcc 48
  · exact hroot.hOcc 49
  · exact hroot.hOcc 50
  · exact hroot.hOcc 51
  · exact hroot.hOcc 60
  · exact hroot.hOcc 62
  · exact hroot.hOcc 63
  · exact hroot.hOcc 71
  · exact hroot.hOcc 73
  · exact hroot.hOcc 76
  · exact hroot.hOcc 78
  · exact hroot.hOcc 83
  · exact hroot.hOcc 84
  · exact hroot.hOcc 85
  · exact hroot.hOcc 86
  · exact hroot.hOcc 91
  · exact hroot.hOcc 92
  · exact hroot.hOcc 95
  · exact hroot.hOcc 97
  · exact hroot.hOcc 98
  · exact hroot.hOcc 100
  · exact hroot.hOcc 102
  · exact hroot.hOcc 103
  · exact hroot.hOcc 105
  · exact hroot.hOcc 106
  · exact hroot.hOcc 107
  · change (∑ j, (-1 : Int) * x j) ≤ -plane452GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 35) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (10 : Fin 35) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (7 : Fin 35) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 35) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0

end QiushiMatmul
