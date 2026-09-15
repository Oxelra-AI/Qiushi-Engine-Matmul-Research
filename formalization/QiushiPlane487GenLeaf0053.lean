import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0053Refs : Fin 49 → RowRef 668 48 := ![.occ 87, .occ 89, .occ 93, .occ 103, .occ 108, .occ 109, .occ 118, .occ 188, .occ 193, .occ 211, .occ 216, .occ 246, .occ 294, .occ 315, .occ 343, .occ 347, .occ 391, .occ 405, .occ 408, .occ 411, .occ 466, .occ 472, .occ 493, .occ 498, .occ 523, .occ 544, .occ 546, .occ 595, .occ 604, .occ 608, .occ 619, .occ 633, .occ 648, .occ 650, .occ 661, .occ 665, .sumGe, .branchGe 39 (1), .branchLe 7 (0), .branchLe 28 (0), .branchLe 40 (0), .branchLe 29 (0), .branchLe 19 (0), .branchLe 36 (0), .branchLe 23 (0), .branchLe 45 (0), .branchGe 5 (1), .branchGe 1 (1), .branchLe 26 (0)]

def plane487GenLeaf0053Mult : Fin 49 → Nat := ![100821, 8109, 28577, 16295, 74022, 174651, 124004, 24670, 57205, 135662, 215919, 79008, 1224, 66616, 79717, 52178, 184116, 153538, 85849, 136511, 84214, 190278, 40852, 58323, 44780, 97443, 50770, 10211, 6614, 21240, 2694, 58361, 19602, 636, 81282, 13669, 422257, 464517, 6361, 229863, 191127, 290868, 271600, 339210, 314789, 363896, 1194151, 357663, 336635]

theorem plane487GenLeaf0053 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_45 : x 45 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0053Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0053Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0053Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0053Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 89
  · exact hroot.hOcc 93
  · exact hroot.hOcc 103
  · exact hroot.hOcc 108
  · exact hroot.hOcc 109
  · exact hroot.hOcc 118
  · exact hroot.hOcc 188
  · exact hroot.hOcc 193
  · exact hroot.hOcc 211
  · exact hroot.hOcc 216
  · exact hroot.hOcc 246
  · exact hroot.hOcc 294
  · exact hroot.hOcc 315
  · exact hroot.hOcc 343
  · exact hroot.hOcc 347
  · exact hroot.hOcc 391
  · exact hroot.hOcc 405
  · exact hroot.hOcc 408
  · exact hroot.hOcc 411
  · exact hroot.hOcc 466
  · exact hroot.hOcc 472
  · exact hroot.hOcc 493
  · exact hroot.hOcc 498
  · exact hroot.hOcc 523
  · exact hroot.hOcc 544
  · exact hroot.hOcc 546
  · exact hroot.hOcc 595
  · exact hroot.hOcc 604
  · exact hroot.hOcc 608
  · exact hroot.hOcc 619
  · exact hroot.hOcc 633
  · exact hroot.hOcc 648
  · exact hroot.hOcc 650
  · exact hroot.hOcc 661
  · exact hroot.hOcc 665
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (39 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (7 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (28 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (40 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (29 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (19 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (36 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (45 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_45
  · change (∑ k, (if k = (5 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5
  · change (∑ k, (if k = (1 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (26 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26

end QiushiMatmul
