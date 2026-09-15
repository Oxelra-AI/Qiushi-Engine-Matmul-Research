import QiushiPlane462GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane462GenLeaf0016Refs : Fin 52 → RowRef 294 62 := ![.occ 19, .occ 21, .occ 23, .occ 24, .occ 28, .occ 30, .occ 32, .occ 33, .occ 36, .occ 39, .occ 41, .occ 55, .occ 68, .occ 70, .occ 71, .occ 74, .occ 75, .occ 77, .occ 78, .occ 80, .occ 81, .occ 89, .occ 91, .occ 96, .occ 97, .occ 100, .occ 101, .occ 102, .occ 108, .occ 136, .occ 167, .occ 221, .occ 244, .occ 260, .occ 270, .occ 272, .occ 278, .occ 283, .occ 289, .occ 291, .sumGe, .nonneg 7, .nonneg 53, .nonneg 59, .branchGe 3 (1), .branchGe 5 (1), .branchGe 24 (1), .branchGe 27 (1), .branchLe 9 (0), .branchGe 16 (1), .branchLe 1 (0), .branchLe 34 (1)]

def plane462GenLeaf0016Mult : Fin 52 → Nat := ![40, 32, 64, 40, 16, 72, 44, 60, 16, 28, 68, 16, 8, 16, 16, 8, 16, 8, 80, 68, 28, 4, 20, 16, 8, 4, 32, 20, 16, 16, 8, 16, 46, 18, 19, 9, 10, 54, 5, 15, 128, 312, 32, 32, 88, 40, 432, 128, 120, 336, 120, 64]

theorem plane462GenLeaf0016 (x : Fin 62 → Int)
    (hroot : plane462GenOccSys.RootHolds x)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (1 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane462GenLeaf0016Refs i).resolveCoeff plane462GenOccSys j)
    (fun i => (plane462GenLeaf0016Refs i).resolveRhs plane462GenOccSys) plane462GenLeaf0016Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane462GenLeaf0016Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 19
  · exact hroot.hOcc 21
  · exact hroot.hOcc 23
  · exact hroot.hOcc 24
  · exact hroot.hOcc 28
  · exact hroot.hOcc 30
  · exact hroot.hOcc 32
  · exact hroot.hOcc 33
  · exact hroot.hOcc 36
  · exact hroot.hOcc 39
  · exact hroot.hOcc 41
  · exact hroot.hOcc 55
  · exact hroot.hOcc 68
  · exact hroot.hOcc 70
  · exact hroot.hOcc 71
  · exact hroot.hOcc 74
  · exact hroot.hOcc 75
  · exact hroot.hOcc 77
  · exact hroot.hOcc 78
  · exact hroot.hOcc 80
  · exact hroot.hOcc 81
  · exact hroot.hOcc 89
  · exact hroot.hOcc 91
  · exact hroot.hOcc 96
  · exact hroot.hOcc 97
  · exact hroot.hOcc 100
  · exact hroot.hOcc 101
  · exact hroot.hOcc 102
  · exact hroot.hOcc 108
  · exact hroot.hOcc 136
  · exact hroot.hOcc 167
  · exact hroot.hOcc 221
  · exact hroot.hOcc 244
  · exact hroot.hOcc 260
  · exact hroot.hOcc 270
  · exact hroot.hOcc 272
  · exact hroot.hOcc 278
  · exact hroot.hOcc 283
  · exact hroot.hOcc 289
  · exact hroot.hOcc 291
  · change (∑ j, (-1 : Int) * x j) ≤ -plane462GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (53 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (59 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (3 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3
  · change (∑ k, (if k = (5 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5
  · change (∑ k, (if k = (24 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24
  · change (∑ k, (if k = (27 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (9 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (16 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (1 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (34 : Fin 62) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_34

end QiushiMatmul
