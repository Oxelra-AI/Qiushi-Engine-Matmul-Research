import QiushiPlane282GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane282GenLeaf0015Refs : Fin 28 → RowRef 100 28 := ![.occ 4, .occ 9, .occ 37, .occ 40, .occ 41, .occ 44, .occ 60, .occ 61, .occ 63, .occ 65, .occ 73, .occ 74, .occ 76, .occ 77, .occ 87, .occ 88, .occ 90, .occ 92, .sumGe, .nonneg 17, .nonneg 20, .nonneg 26, .branchLe 12 (0), .branchLe 4 (1), .branchLe 18 (0), .branchLe 19 (0), .branchGe 22 (2), .branchGe 2 (2)]

def plane282GenLeaf0015Mult : Fin 28 → Nat := ![12, 11, 4, 11, 6, 4, 2, 6, 5, 1, 1, 6, 4, 11, 7, 6, 11, 1, 23, 6, 11, 3, 9, 5, 1, 4, 16, 24]

theorem plane282GenLeaf0015 (x : Fin 28 → Int)
    (hroot : plane282GenOccSys.RootHolds x)
    (hLB_0 : (3 : Int) ≤ x 0)
    (hLB_2 : (2 : Int) ≤ x 2)
    (hLB_22 : (2 : Int) ≤ x 22)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (1 : Int))
    (hUB_8 : x 8 ≤ (1 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane282GenLeaf0015Refs i).resolveCoeff plane282GenOccSys j)
    (fun i => (plane282GenLeaf0015Refs i).resolveRhs plane282GenOccSys) plane282GenLeaf0015Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane282GenLeaf0015Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 4
  · exact hroot.hOcc 9
  · exact hroot.hOcc 37
  · exact hroot.hOcc 40
  · exact hroot.hOcc 41
  · exact hroot.hOcc 44
  · exact hroot.hOcc 60
  · exact hroot.hOcc 61
  · exact hroot.hOcc 63
  · exact hroot.hOcc 65
  · exact hroot.hOcc 73
  · exact hroot.hOcc 74
  · exact hroot.hOcc 76
  · exact hroot.hOcc 77
  · exact hroot.hOcc 87
  · exact hroot.hOcc 88
  · exact hroot.hOcc 90
  · exact hroot.hOcc 92
  · change (∑ j, (-1 : Int) * x j) ≤ -plane282GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (17 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (20 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (26 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (12 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (4 : Fin 28) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (18 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (19 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (22 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22
  · change (∑ k, (if k = (2 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2

end QiushiMatmul
