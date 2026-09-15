import QiushiPlane480GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane480GenLeaf0017Refs : Fin 19 → RowRef 221 26 := ![.occ 103, .occ 112, .occ 117, .occ 118, .occ 127, .occ 130, .occ 142, .occ 143, .occ 146, .occ 169, .occ 195, .occ 210, .occ 214, .sumGe, .branchLe 14 (0), .branchGe 11 (1), .branchLe 12 (0), .branchLe 17 (0), .branchGe 10 (1)]

def plane480GenLeaf0017Mult : Fin 19 → Nat := ![1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4]

theorem plane480GenLeaf0017 (x : Fin 26 → Int)
    (hroot : plane480GenOccSys.RootHolds x)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane480GenLeaf0017Refs i).resolveCoeff plane480GenOccSys j)
    (fun i => (plane480GenLeaf0017Refs i).resolveRhs plane480GenOccSys) plane480GenLeaf0017Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane480GenLeaf0017Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 103
  · exact hroot.hOcc 112
  · exact hroot.hOcc 117
  · exact hroot.hOcc 118
  · exact hroot.hOcc 127
  · exact hroot.hOcc 130
  · exact hroot.hOcc 142
  · exact hroot.hOcc 143
  · exact hroot.hOcc 146
  · exact hroot.hOcc 169
  · exact hroot.hOcc 195
  · exact hroot.hOcc 210
  · exact hroot.hOcc 214
  · change (∑ j, (-1 : Int) * x j) ≤ -plane480GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (11 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11
  · change (∑ k, (if k = (12 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (17 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (10 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10

end QiushiMatmul
