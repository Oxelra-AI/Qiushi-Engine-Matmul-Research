import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0035Refs : Fin 33 → RowRef 371 32 := ![.occ 95, .occ 100, .occ 102, .occ 146, .occ 147, .occ 165, .occ 190, .occ 201, .occ 202, .occ 207, .occ 208, .occ 273, .occ 275, .occ 310, .occ 318, .occ 327, .occ 333, .occ 334, .occ 337, .occ 341, .occ 342, .occ 344, .occ 348, .occ 360, .sumGe, .nonneg 10, .nonneg 16, .branchGe 14 (1), .branchLe 26 (0), .branchGe 7 (1), .branchLe 18 (0), .branchGe 31 (1), .branchGe 23 (1)]

def plane489GenLeaf0035Mult : Fin 33 → Nat := ![38, 7, 15, 10, 8, 2, 24, 35, 5, 11, 26, 25, 20, 8, 37, 52, 1, 21, 30, 9, 70, 46, 62, 9, 116, 9, 103, 123, 91, 125, 38, 221, 239]

theorem plane489GenLeaf0035 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0035Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0035Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0035Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0035Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 95
  · exact hroot.hOcc 100
  · exact hroot.hOcc 102
  · exact hroot.hOcc 146
  · exact hroot.hOcc 147
  · exact hroot.hOcc 165
  · exact hroot.hOcc 190
  · exact hroot.hOcc 201
  · exact hroot.hOcc 202
  · exact hroot.hOcc 207
  · exact hroot.hOcc 208
  · exact hroot.hOcc 273
  · exact hroot.hOcc 275
  · exact hroot.hOcc 310
  · exact hroot.hOcc 318
  · exact hroot.hOcc 327
  · exact hroot.hOcc 333
  · exact hroot.hOcc 334
  · exact hroot.hOcc 337
  · exact hroot.hOcc 341
  · exact hroot.hOcc 342
  · exact hroot.hOcc 344
  · exact hroot.hOcc 348
  · exact hroot.hOcc 360
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 32) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (16 : Fin 32) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (14 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (26 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (7 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (18 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (31 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (23 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23

end QiushiMatmul
