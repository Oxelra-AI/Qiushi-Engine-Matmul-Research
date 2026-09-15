import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0060Refs : Fin 49 → RowRef 668 48 := ![.occ 84, .occ 85, .occ 87, .occ 99, .occ 102, .occ 152, .occ 160, .occ 216, .occ 222, .occ 225, .occ 234, .occ 235, .occ 246, .occ 254, .occ 258, .occ 260, .occ 313, .occ 315, .occ 321, .occ 335, .occ 351, .occ 371, .occ 377, .occ 391, .occ 437, .occ 523, .occ 531, .occ 539, .occ 563, .occ 589, .occ 595, .occ 621, .occ 644, .occ 645, .occ 648, .occ 650, .sumGe, .nonneg 0, .nonneg 7, .nonneg 8, .nonneg 36, .branchGe 39 (1), .branchLe 28 (0), .branchLe 40 (0), .branchLe 29 (0), .branchLe 19 (0), .branchGe 23 (1), .branchLe 10 (0), .branchGe 16 (1)]

def plane487GenLeaf0060Mult : Fin 49 → Nat := ![4531, 73, 19866, 38289, 80917, 12758, 32071, 14585, 1639, 3596, 4545, 10832, 27153, 3208, 10703, 27320, 361, 10923, 5115, 50575, 50727, 7121, 35453, 12442, 37360, 3844, 693, 22661, 12279, 13100, 4042, 11487, 8902, 32066, 3250, 13001, 90180, 8648, 4106, 41103, 9157, 140688, 90180, 77540, 45269, 62214, 184476, 40668, 260444]

theorem plane487GenLeaf0060 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0060Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0060Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0060Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0060Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 84
  · exact hroot.hOcc 85
  · exact hroot.hOcc 87
  · exact hroot.hOcc 99
  · exact hroot.hOcc 102
  · exact hroot.hOcc 152
  · exact hroot.hOcc 160
  · exact hroot.hOcc 216
  · exact hroot.hOcc 222
  · exact hroot.hOcc 225
  · exact hroot.hOcc 234
  · exact hroot.hOcc 235
  · exact hroot.hOcc 246
  · exact hroot.hOcc 254
  · exact hroot.hOcc 258
  · exact hroot.hOcc 260
  · exact hroot.hOcc 313
  · exact hroot.hOcc 315
  · exact hroot.hOcc 321
  · exact hroot.hOcc 335
  · exact hroot.hOcc 351
  · exact hroot.hOcc 371
  · exact hroot.hOcc 377
  · exact hroot.hOcc 391
  · exact hroot.hOcc 437
  · exact hroot.hOcc 523
  · exact hroot.hOcc 531
  · exact hroot.hOcc 539
  · exact hroot.hOcc 563
  · exact hroot.hOcc 589
  · exact hroot.hOcc 595
  · exact hroot.hOcc 621
  · exact hroot.hOcc 644
  · exact hroot.hOcc 645
  · exact hroot.hOcc 648
  · exact hroot.hOcc 650
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (7 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (8 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (36 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (39 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (28 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (40 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (29 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (19 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (23 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (10 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (16 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16

end QiushiMatmul
