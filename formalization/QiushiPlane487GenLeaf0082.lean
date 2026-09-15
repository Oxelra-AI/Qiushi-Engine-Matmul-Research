import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0082Refs : Fin 49 → RowRef 668 48 := ![.occ 83, .occ 89, .occ 95, .occ 99, .occ 104, .occ 142, .occ 163, .occ 171, .occ 177, .occ 237, .occ 239, .occ 243, .occ 246, .occ 260, .occ 263, .occ 288, .occ 303, .occ 308, .occ 312, .occ 380, .occ 386, .occ 401, .occ 443, .occ 451, .occ 482, .occ 488, .occ 490, .occ 502, .occ 519, .occ 523, .occ 598, .occ 604, .occ 608, .occ 661, .occ 662, .occ 665, .occ 666, .sumGe, .nonneg 8, .nonneg 21, .nonneg 40, .nonneg 47, .branchGe 39 (1), .branchLe 7 (0), .branchGe 28 (1), .branchLe 3 (0), .branchLe 36 (0), .branchGe 35 (1), .branchLe 19 (0)]

def plane487GenLeaf0082Mult : Fin 49 → Nat := ![7929, 16626, 32346, 8635, 5446, 22229, 31272, 10595, 47135, 41498, 3790, 25108, 7319, 9110, 17791, 20985, 366, 7968, 12708, 37488, 51943, 33211, 20274, 2782, 3921, 34449, 2293, 2681, 732, 16446, 44368, 1198, 10042, 6443, 1393, 8383, 10042, 85682, 8184, 28031, 86853, 22174, 78888, 31421, 294408, 61646, 77348, 213418, 54921]

theorem plane487GenLeaf0082 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_36 : x 36 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0082Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0082Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0082Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0082Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 83
  · exact hroot.hOcc 89
  · exact hroot.hOcc 95
  · exact hroot.hOcc 99
  · exact hroot.hOcc 104
  · exact hroot.hOcc 142
  · exact hroot.hOcc 163
  · exact hroot.hOcc 171
  · exact hroot.hOcc 177
  · exact hroot.hOcc 237
  · exact hroot.hOcc 239
  · exact hroot.hOcc 243
  · exact hroot.hOcc 246
  · exact hroot.hOcc 260
  · exact hroot.hOcc 263
  · exact hroot.hOcc 288
  · exact hroot.hOcc 303
  · exact hroot.hOcc 308
  · exact hroot.hOcc 312
  · exact hroot.hOcc 380
  · exact hroot.hOcc 386
  · exact hroot.hOcc 401
  · exact hroot.hOcc 443
  · exact hroot.hOcc 451
  · exact hroot.hOcc 482
  · exact hroot.hOcc 488
  · exact hroot.hOcc 490
  · exact hroot.hOcc 502
  · exact hroot.hOcc 519
  · exact hroot.hOcc 523
  · exact hroot.hOcc 598
  · exact hroot.hOcc 604
  · exact hroot.hOcc 608
  · exact hroot.hOcc 661
  · exact hroot.hOcc 662
  · exact hroot.hOcc 665
  · exact hroot.hOcc 666
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (21 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (40 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (47 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (39 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (7 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (28 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (3 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (36 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (35 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (19 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19

end QiushiMatmul
