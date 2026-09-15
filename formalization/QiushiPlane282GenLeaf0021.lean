import QiushiPlane282GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane282GenLeaf0021Refs : Fin 25 → RowRef 100 28 := ![.occ 4, .occ 9, .occ 20, .occ 35, .occ 40, .occ 41, .occ 44, .occ 47, .occ 51, .occ 56, .occ 61, .occ 62, .occ 63, .occ 86, .occ 88, .occ 90, .sumGe, .nonneg 20, .nonneg 26, .branchLe 12 (0), .branchLe 4 (1), .branchLe 19 (0), .branchGe 22 (2), .branchGe 8 (2), .branchGe 9 (1)]

def plane282GenLeaf0021Mult : Fin 25 → Nat := ![2, 6, 12, 3, 2, 2, 6, 2, 1, 2, 10, 1, 8, 1, 4, 4, 12, 10, 8, 4, 8, 2, 12, 4, 22]

theorem plane282GenLeaf0021 (x : Fin 28 → Int)
    (hroot : plane282GenOccSys.RootHolds x)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hLB_22 : (2 : Int) ≤ x 22)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_8 : (2 : Int) ≤ x 8)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (1 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane282GenLeaf0021Refs i).resolveCoeff plane282GenOccSys j)
    (fun i => (plane282GenLeaf0021Refs i).resolveRhs plane282GenOccSys) plane282GenLeaf0021Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane282GenLeaf0021Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 4
  · exact hroot.hOcc 9
  · exact hroot.hOcc 20
  · exact hroot.hOcc 35
  · exact hroot.hOcc 40
  · exact hroot.hOcc 41
  · exact hroot.hOcc 44
  · exact hroot.hOcc 47
  · exact hroot.hOcc 51
  · exact hroot.hOcc 56
  · exact hroot.hOcc 61
  · exact hroot.hOcc 62
  · exact hroot.hOcc 63
  · exact hroot.hOcc 86
  · exact hroot.hOcc 88
  · exact hroot.hOcc 90
  · change (∑ j, (-1 : Int) * x j) ≤ -plane282GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (20 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (26 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (12 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (4 : Fin 28) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (19 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (22 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22
  · change (∑ k, (if k = (8 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8
  · change (∑ k, (if k = (9 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9

end QiushiMatmul
