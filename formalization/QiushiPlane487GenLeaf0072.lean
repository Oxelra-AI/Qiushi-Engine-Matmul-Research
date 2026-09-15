import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0072Refs : Fin 37 → RowRef 668 48 := ![.occ 101, .occ 106, .occ 146, .occ 184, .occ 190, .occ 193, .occ 240, .occ 253, .occ 275, .occ 280, .occ 307, .occ 308, .occ 328, .occ 353, .occ 355, .occ 357, .occ 362, .occ 399, .occ 413, .occ 436, .occ 448, .occ 459, .occ 499, .occ 546, .occ 558, .occ 566, .occ 573, .occ 596, .occ 648, .sumGe, .nonneg 0, .nonneg 20, .branchGe 39 (1), .branchLe 7 (0), .branchLe 40 (0), .branchGe 29 (1), .branchGe 10 (1)]

def plane487GenLeaf0072Mult : Fin 37 → Nat := ![71, 19, 98, 23, 34, 34, 266, 34, 131, 135, 11, 34, 56, 9, 56, 13, 147, 76, 38, 13, 26, 94, 37, 85, 49, 38, 37, 122, 97, 266, 34, 1, 34, 137, 61, 1458, 1074]

theorem plane487GenLeaf0072 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0072Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0072Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0072Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0072Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 101
  · exact hroot.hOcc 106
  · exact hroot.hOcc 146
  · exact hroot.hOcc 184
  · exact hroot.hOcc 190
  · exact hroot.hOcc 193
  · exact hroot.hOcc 240
  · exact hroot.hOcc 253
  · exact hroot.hOcc 275
  · exact hroot.hOcc 280
  · exact hroot.hOcc 307
  · exact hroot.hOcc 308
  · exact hroot.hOcc 328
  · exact hroot.hOcc 353
  · exact hroot.hOcc 355
  · exact hroot.hOcc 357
  · exact hroot.hOcc 362
  · exact hroot.hOcc 399
  · exact hroot.hOcc 413
  · exact hroot.hOcc 436
  · exact hroot.hOcc 448
  · exact hroot.hOcc 459
  · exact hroot.hOcc 499
  · exact hroot.hOcc 546
  · exact hroot.hOcc 558
  · exact hroot.hOcc 566
  · exact hroot.hOcc 573
  · exact hroot.hOcc 596
  · exact hroot.hOcc 648
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (20 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (39 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (7 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (40 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (29 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (10 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10

end QiushiMatmul
