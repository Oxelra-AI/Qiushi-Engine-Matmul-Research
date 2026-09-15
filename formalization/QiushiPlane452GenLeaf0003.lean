import QiushiPlane452GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane452GenLeaf0003Refs : Fin 31 → RowRef 117 35 := ![.occ 28, .occ 34, .occ 36, .occ 38, .occ 39, .occ 40, .occ 42, .occ 46, .occ 49, .occ 57, .occ 59, .occ 61, .occ 65, .occ 67, .occ 70, .occ 75, .occ 80, .occ 81, .occ 83, .occ 84, .occ 86, .occ 87, .occ 89, .occ 93, .occ 94, .occ 99, .occ 108, .occ 112, .sumGe, .branchLe 8 (0), .branchGe 10 (1)]

def plane452GenLeaf0003Mult : Fin 31 → Nat := ![6, 2, 6, 2, 3, 4, 2, 6, 4, 4, 4, 2, 3, 3, 6, 2, 6, 3, 1, 2, 2, 3, 1, 2, 3, 2, 2, 4, 6, 6, 36]

theorem plane452GenLeaf0003 (x : Fin 35 → Int)
    (hroot : plane452GenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hUB_8 : x 8 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane452GenLeaf0003Refs i).resolveCoeff plane452GenOccSys j)
    (fun i => (plane452GenLeaf0003Refs i).resolveRhs plane452GenOccSys) plane452GenLeaf0003Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane452GenLeaf0003Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 28
  · exact hroot.hOcc 34
  · exact hroot.hOcc 36
  · exact hroot.hOcc 38
  · exact hroot.hOcc 39
  · exact hroot.hOcc 40
  · exact hroot.hOcc 42
  · exact hroot.hOcc 46
  · exact hroot.hOcc 49
  · exact hroot.hOcc 57
  · exact hroot.hOcc 59
  · exact hroot.hOcc 61
  · exact hroot.hOcc 65
  · exact hroot.hOcc 67
  · exact hroot.hOcc 70
  · exact hroot.hOcc 75
  · exact hroot.hOcc 80
  · exact hroot.hOcc 81
  · exact hroot.hOcc 83
  · exact hroot.hOcc 84
  · exact hroot.hOcc 86
  · exact hroot.hOcc 87
  · exact hroot.hOcc 89
  · exact hroot.hOcc 93
  · exact hroot.hOcc 94
  · exact hroot.hOcc 99
  · exact hroot.hOcc 108
  · exact hroot.hOcc 112
  · change (∑ j, (-1 : Int) * x j) ≤ -plane452GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 35) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (10 : Fin 35) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10

end QiushiMatmul
