import QiushiPlane452GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane452GenLeaf0002Refs : Fin 32 → RowRef 117 35 := ![.occ 31, .occ 32, .occ 34, .occ 41, .occ 44, .occ 47, .occ 54, .occ 55, .occ 58, .occ 60, .occ 63, .occ 64, .occ 66, .occ 67, .occ 72, .occ 81, .occ 83, .occ 85, .occ 86, .occ 87, .occ 88, .occ 90, .occ 91, .occ 95, .occ 99, .occ 104, .occ 106, .occ 107, .sumGe, .branchLe 8 (0), .branchLe 10 (0), .branchGe 7 (1)]

def plane452GenLeaf0002Mult : Fin 32 → Nat := ![12, 4, 12, 10, 8, 6, 6, 12, 2, 8, 3, 12, 3, 9, 6, 4, 4, 4, 4, 4, 4, 4, 2, 6, 4, 12, 6, 6, 12, 12, 12, 58]

theorem plane452GenLeaf0002 (x : Fin 35 → Int)
    (hroot : plane452GenOccSys.RootHolds x)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane452GenLeaf0002Refs i).resolveCoeff plane452GenOccSys j)
    (fun i => (plane452GenLeaf0002Refs i).resolveRhs plane452GenOccSys) plane452GenLeaf0002Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane452GenLeaf0002Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 31
  · exact hroot.hOcc 32
  · exact hroot.hOcc 34
  · exact hroot.hOcc 41
  · exact hroot.hOcc 44
  · exact hroot.hOcc 47
  · exact hroot.hOcc 54
  · exact hroot.hOcc 55
  · exact hroot.hOcc 58
  · exact hroot.hOcc 60
  · exact hroot.hOcc 63
  · exact hroot.hOcc 64
  · exact hroot.hOcc 66
  · exact hroot.hOcc 67
  · exact hroot.hOcc 72
  · exact hroot.hOcc 81
  · exact hroot.hOcc 83
  · exact hroot.hOcc 85
  · exact hroot.hOcc 86
  · exact hroot.hOcc 87
  · exact hroot.hOcc 88
  · exact hroot.hOcc 90
  · exact hroot.hOcc 91
  · exact hroot.hOcc 95
  · exact hroot.hOcc 99
  · exact hroot.hOcc 104
  · exact hroot.hOcc 106
  · exact hroot.hOcc 107
  · change (∑ j, (-1 : Int) * x j) ≤ -plane452GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 35) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (10 : Fin 35) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (7 : Fin 35) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7

end QiushiMatmul
