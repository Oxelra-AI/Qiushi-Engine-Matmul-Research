import QiushiPlane452GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane452GenLeaf0001Refs : Fin 19 → RowRef 117 35 := ![.occ 40, .occ 50, .occ 52, .occ 56, .occ 69, .occ 71, .occ 76, .occ 82, .occ 87, .occ 92, .occ 96, .occ 107, .occ 115, .occ 116, .sumGe, .branchLe 8 (0), .branchLe 10 (0), .branchLe 7 (0), .branchGe 0 (1)]

def plane452GenLeaf0001Mult : Fin 19 → Nat := ![1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4]

theorem plane452GenLeaf0001 (x : Fin 35 → Int)
    (hroot : plane452GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane452GenLeaf0001Refs i).resolveCoeff plane452GenOccSys j)
    (fun i => (plane452GenLeaf0001Refs i).resolveRhs plane452GenOccSys) plane452GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane452GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 40
  · exact hroot.hOcc 50
  · exact hroot.hOcc 52
  · exact hroot.hOcc 56
  · exact hroot.hOcc 69
  · exact hroot.hOcc 71
  · exact hroot.hOcc 76
  · exact hroot.hOcc 82
  · exact hroot.hOcc 87
  · exact hroot.hOcc 92
  · exact hroot.hOcc 96
  · exact hroot.hOcc 107
  · exact hroot.hOcc 115
  · exact hroot.hOcc 116
  · change (∑ j, (-1 : Int) * x j) ≤ -plane452GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 35) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (10 : Fin 35) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (7 : Fin 35) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 35) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
