import QiushiPlane282GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane282GenLeaf0026Refs : Fin 26 → RowRef 100 28 := ![.occ 4, .occ 9, .occ 19, .occ 21, .occ 28, .occ 38, .occ 44, .occ 47, .occ 51, .occ 58, .occ 60, .occ 61, .occ 63, .occ 65, .occ 74, .occ 86, .occ 87, .occ 88, .occ 90, .sumGe, .nonneg 13, .nonneg 16, .branchLe 4 (1), .branchGe 18 (1), .branchLe 19 (0), .branchLe 11 (0)]

def plane282GenLeaf0026Mult : Fin 26 → Nat := ![8, 18, 2, 12, 2, 9, 1, 15, 1, 1, 2, 5, 14, 5, 10, 1, 3, 4, 3, 22, 8, 2, 16, 42, 4, 14]

theorem plane282GenLeaf0026 (x : Fin 28 → Int)
    (hroot : plane282GenOccSys.RootHolds x)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (1 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane282GenLeaf0026Refs i).resolveCoeff plane282GenOccSys j)
    (fun i => (plane282GenLeaf0026Refs i).resolveRhs plane282GenOccSys) plane282GenLeaf0026Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane282GenLeaf0026Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 4
  · exact hroot.hOcc 9
  · exact hroot.hOcc 19
  · exact hroot.hOcc 21
  · exact hroot.hOcc 28
  · exact hroot.hOcc 38
  · exact hroot.hOcc 44
  · exact hroot.hOcc 47
  · exact hroot.hOcc 51
  · exact hroot.hOcc 58
  · exact hroot.hOcc 60
  · exact hroot.hOcc 61
  · exact hroot.hOcc 63
  · exact hroot.hOcc 65
  · exact hroot.hOcc 74
  · exact hroot.hOcc 86
  · exact hroot.hOcc 87
  · exact hroot.hOcc 88
  · exact hroot.hOcc 90
  · change (∑ j, (-1 : Int) * x j) ≤ -plane282GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (13 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (16 : Fin 28) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (4 : Fin 28) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (18 : Fin 28) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (19 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (11 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11

end QiushiMatmul
