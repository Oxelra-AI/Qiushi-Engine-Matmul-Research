import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0078Refs : Fin 49 → RowRef 668 48 := ![.occ 83, .occ 94, .occ 100, .occ 147, .occ 167, .occ 199, .occ 201, .occ 209, .occ 217, .occ 237, .occ 238, .occ 239, .occ 260, .occ 271, .occ 295, .occ 302, .occ 303, .occ 312, .occ 315, .occ 347, .occ 353, .occ 378, .occ 386, .occ 389, .occ 391, .occ 401, .occ 420, .occ 487, .occ 489, .occ 490, .occ 499, .occ 512, .occ 547, .occ 655, .occ 661, .occ 665, .sumGe, .nonneg 8, .nonneg 27, .nonneg 47, .branchGe 39 (1), .branchLe 7 (0), .branchGe 28 (1), .branchLe 3 (0), .branchLe 36 (0), .branchLe 35 (0), .branchLe 13 (0), .branchLe 37 (0), .branchGe 38 (1)]

def plane487GenLeaf0078Mult : Fin 49 → Nat := ![764, 519, 739, 1258, 1430, 1021, 1165, 652, 626, 2914, 793, 486, 923, 401, 706, 87, 658, 184, 842, 1819, 205, 756, 2562, 1388, 335, 1888, 270, 303, 118, 1451, 658, 49, 993, 695, 572, 1365, 4937, 901, 490, 713, 4444, 1172, 10880, 2563, 2591, 2040, 4365, 3000, 11755]

theorem plane487GenLeaf0078 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_37 : x 37 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0078Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0078Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0078Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0078Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 83
  · exact hroot.hOcc 94
  · exact hroot.hOcc 100
  · exact hroot.hOcc 147
  · exact hroot.hOcc 167
  · exact hroot.hOcc 199
  · exact hroot.hOcc 201
  · exact hroot.hOcc 209
  · exact hroot.hOcc 217
  · exact hroot.hOcc 237
  · exact hroot.hOcc 238
  · exact hroot.hOcc 239
  · exact hroot.hOcc 260
  · exact hroot.hOcc 271
  · exact hroot.hOcc 295
  · exact hroot.hOcc 302
  · exact hroot.hOcc 303
  · exact hroot.hOcc 312
  · exact hroot.hOcc 315
  · exact hroot.hOcc 347
  · exact hroot.hOcc 353
  · exact hroot.hOcc 378
  · exact hroot.hOcc 386
  · exact hroot.hOcc 389
  · exact hroot.hOcc 391
  · exact hroot.hOcc 401
  · exact hroot.hOcc 420
  · exact hroot.hOcc 487
  · exact hroot.hOcc 489
  · exact hroot.hOcc 490
  · exact hroot.hOcc 499
  · exact hroot.hOcc 512
  · exact hroot.hOcc 547
  · exact hroot.hOcc 655
  · exact hroot.hOcc 661
  · exact hroot.hOcc 665
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (27 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27
  · change (∑ k, (if k = (47 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (39 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (7 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (28 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (3 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (36 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (35 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (13 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (37 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (38 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38

end QiushiMatmul
