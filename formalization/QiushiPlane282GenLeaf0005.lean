import QiushiPlane282GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane282GenLeaf0005Refs : Fin 29 → RowRef 100 28 := ![.occ 4, .occ 9, .occ 20, .occ 34, .occ 35, .occ 42, .occ 44, .occ 47, .occ 48, .occ 60, .occ 65, .occ 69, .occ 76, .occ 77, .occ 88, .occ 90, .occ 98, .sumGe, .nonneg 5, .nonneg 11, .nonneg 20, .nonneg 21, .branchLe 12 (0), .branchLe 18 (0), .branchLe 19 (0), .branchLe 22 (1), .branchLe 25 (0), .branchGe 1 (1), .branchLe 6 (1)]

def plane282GenLeaf0005Mult : Fin 29 → Nat := ![70, 62, 28, 29, 11, 7, 13, 2, 31, 19, 4, 36, 30, 29, 42, 58, 12, 123, 16, 20, 8, 16, 24, 92, 92, 56, 104, 12, 52]

theorem plane282GenLeaf0005 (x : Fin 28 → Int)
    (hroot : plane282GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (1 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (1 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane282GenLeaf0005Refs i).resolveCoeff plane282GenOccSys j)
    (fun i => (plane282GenLeaf0005Refs i).resolveRhs plane282GenOccSys) plane282GenLeaf0005Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane282GenLeaf0005Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 4
  · exact hroot.hOcc 9
  · exact hroot.hOcc 20
  · exact hroot.hOcc 34
  · exact hroot.hOcc 35
  · exact hroot.hOcc 42
  · exact hroot.hOcc 44
  · exact hroot.hOcc 47
  · exact hroot.hOcc 48
  · exact hroot.hOcc 60
  · exact hroot.hOcc 65
  · exact hroot.hOcc 69
  · exact hroot.hOcc 76
  · exact hroot.hOcc 77
  · exact hroot.hOcc 88
  · exact hroot.hOcc 90
  · exact hroot.hOcc 98
  · change (∑ j, (-1 : Int) * x j) ≤ -plane282GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (5 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (11 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (20 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (21 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (12 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (18 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (19 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (22 : Fin 28) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (25 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (1 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (6 : Fin 28) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_6

end QiushiMatmul
