import QiushiPlane480GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane480GenLeaf0019Refs : Fin 14 → RowRef 221 26 := ![.occ 103, .occ 106, .occ 112, .occ 117, .occ 118, .occ 121, .occ 174, .occ 220, .sumGe, .branchLe 14 (0), .branchGe 11 (1), .branchLe 12 (0), .branchGe 17 (1), .branchGe 10 (1)]

def plane480GenLeaf0019Mult : Fin 14 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2]

theorem plane480GenLeaf0019 (x : Fin 26 → Int)
    (hroot : plane480GenOccSys.RootHolds x)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane480GenLeaf0019Refs i).resolveCoeff plane480GenOccSys j)
    (fun i => (plane480GenLeaf0019Refs i).resolveRhs plane480GenOccSys) plane480GenLeaf0019Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane480GenLeaf0019Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 103
  · exact hroot.hOcc 106
  · exact hroot.hOcc 112
  · exact hroot.hOcc 117
  · exact hroot.hOcc 118
  · exact hroot.hOcc 121
  · exact hroot.hOcc 174
  · exact hroot.hOcc 220
  · change (∑ j, (-1 : Int) * x j) ≤ -plane480GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (11 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11
  · change (∑ k, (if k = (12 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (17 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17
  · change (∑ k, (if k = (10 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10

end QiushiMatmul
