import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0028Refs : Fin 49 → RowRef 668 48 := ![.occ 108, .occ 110, .occ 115, .occ 145, .occ 184, .occ 223, .occ 241, .occ 253, .occ 254, .occ 266, .occ 269, .occ 280, .occ 296, .occ 302, .occ 315, .occ 353, .occ 356, .occ 378, .occ 380, .occ 386, .occ 399, .occ 404, .occ 415, .occ 459, .occ 462, .occ 471, .occ 474, .occ 531, .occ 552, .occ 556, .occ 563, .occ 566, .occ 577, .occ 581, .occ 584, .occ 598, .occ 648, .occ 661, .occ 664, .sumGe, .nonneg 0, .nonneg 45, .branchLe 39 (0), .branchLe 23 (0), .branchGe 6 (1), .branchLe 33 (0), .branchLe 14 (0), .branchGe 29 (1), .branchGe 3 (1)]

def plane487GenLeaf0028Mult : Fin 49 → Nat := ![98326, 513516, 27010, 383055, 456622, 75423, 109175, 229279, 50845, 30962, 78874, 196521, 101220, 181250, 243494, 46765, 129402, 59209, 73764, 224987, 239223, 84338, 78502, 85551, 9796, 20940, 89922, 48389, 233779, 9177, 44093, 82304, 17716, 18243, 29889, 74226, 115747, 66755, 58624, 685245, 402286, 79404, 441547, 105093, 1275624, 215400, 634400, 1521283, 1463601]

theorem plane487GenLeaf0028 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0028Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0028Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0028Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0028Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 108
  · exact hroot.hOcc 110
  · exact hroot.hOcc 115
  · exact hroot.hOcc 145
  · exact hroot.hOcc 184
  · exact hroot.hOcc 223
  · exact hroot.hOcc 241
  · exact hroot.hOcc 253
  · exact hroot.hOcc 254
  · exact hroot.hOcc 266
  · exact hroot.hOcc 269
  · exact hroot.hOcc 280
  · exact hroot.hOcc 296
  · exact hroot.hOcc 302
  · exact hroot.hOcc 315
  · exact hroot.hOcc 353
  · exact hroot.hOcc 356
  · exact hroot.hOcc 378
  · exact hroot.hOcc 380
  · exact hroot.hOcc 386
  · exact hroot.hOcc 399
  · exact hroot.hOcc 404
  · exact hroot.hOcc 415
  · exact hroot.hOcc 459
  · exact hroot.hOcc 462
  · exact hroot.hOcc 471
  · exact hroot.hOcc 474
  · exact hroot.hOcc 531
  · exact hroot.hOcc 552
  · exact hroot.hOcc 556
  · exact hroot.hOcc 563
  · exact hroot.hOcc 566
  · exact hroot.hOcc 577
  · exact hroot.hOcc 581
  · exact hroot.hOcc 584
  · exact hroot.hOcc 598
  · exact hroot.hOcc 648
  · exact hroot.hOcc 661
  · exact hroot.hOcc 664
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (45 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (6 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (33 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (14 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (29 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (3 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3

end QiushiMatmul
