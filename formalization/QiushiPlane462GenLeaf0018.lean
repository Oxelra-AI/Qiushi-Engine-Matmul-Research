import QiushiPlane462GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane462GenLeaf0018Refs : Fin 49 → RowRef 294 62 := ![.occ 34, .occ 35, .occ 45, .occ 59, .occ 67, .occ 71, .occ 74, .occ 78, .occ 80, .occ 81, .occ 85, .occ 96, .occ 109, .occ 163, .occ 168, .occ 182, .occ 191, .occ 193, .occ 200, .occ 240, .occ 274, .occ 275, .occ 286, .occ 287, .occ 292, .sumGe, .nonneg 0, .nonneg 7, .nonneg 8, .nonneg 11, .nonneg 13, .nonneg 29, .nonneg 38, .nonneg 40, .nonneg 46, .nonneg 47, .nonneg 48, .nonneg 49, .nonneg 54, .nonneg 55, .nonneg 56, .nonneg 57, .branchGe 3 (1), .branchGe 5 (1), .branchGe 24 (1), .branchGe 27 (1), .branchLe 9 (0), .branchGe 16 (1), .branchGe 1 (1)]

def plane462GenLeaf0018Mult : Fin 49 → Nat := ![32, 32, 8, 56, 107, 107, 124, 112, 176, 52, 112, 85, 85, 17, 103, 10, 32, 38, 98, 22, 37, 8, 51, 16, 48, 200, 384, 392, 88, 56, 56, 72, 128, 128, 353, 265, 243, 51, 191, 255, 125, 85, 160, 160, 472, 136, 184, 472, 344]

theorem plane462GenLeaf0018 (x : Fin 62 → Int)
    (hroot : plane462GenOccSys.RootHolds x)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hUB_9 : x 9 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane462GenLeaf0018Refs i).resolveCoeff plane462GenOccSys j)
    (fun i => (plane462GenLeaf0018Refs i).resolveRhs plane462GenOccSys) plane462GenLeaf0018Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane462GenLeaf0018Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 34
  · exact hroot.hOcc 35
  · exact hroot.hOcc 45
  · exact hroot.hOcc 59
  · exact hroot.hOcc 67
  · exact hroot.hOcc 71
  · exact hroot.hOcc 74
  · exact hroot.hOcc 78
  · exact hroot.hOcc 80
  · exact hroot.hOcc 81
  · exact hroot.hOcc 85
  · exact hroot.hOcc 96
  · exact hroot.hOcc 109
  · exact hroot.hOcc 163
  · exact hroot.hOcc 168
  · exact hroot.hOcc 182
  · exact hroot.hOcc 191
  · exact hroot.hOcc 193
  · exact hroot.hOcc 200
  · exact hroot.hOcc 240
  · exact hroot.hOcc 274
  · exact hroot.hOcc 275
  · exact hroot.hOcc 286
  · exact hroot.hOcc 287
  · exact hroot.hOcc 292
  · change (∑ j, (-1 : Int) * x j) ≤ -plane462GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (7 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (8 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (11 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (13 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (29 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (38 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (40 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (46 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (47 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (48 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (49 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (54 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 54
  · change (∑ k, (if k = (55 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (56 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 56
  · change (∑ k, (if k = (57 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 57
  · change (∑ k, (if k = (3 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3
  · change (∑ k, (if k = (5 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5
  · change (∑ k, (if k = (24 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24
  · change (∑ k, (if k = (27 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (9 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (16 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (1 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1

end QiushiMatmul
