import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0037Refs : Fin 49 → RowRef 668 48 := ![.occ 82, .occ 83, .occ 86, .occ 92, .occ 118, .occ 119, .occ 128, .occ 148, .occ 178, .occ 206, .occ 227, .occ 230, .occ 263, .occ 296, .occ 300, .occ 303, .occ 308, .occ 312, .occ 316, .occ 322, .occ 347, .occ 352, .occ 377, .occ 378, .occ 382, .occ 386, .occ 435, .occ 446, .occ 469, .occ 470, .occ 471, .occ 490, .occ 521, .occ 529, .occ 530, .occ 546, .occ 572, .occ 633, .occ 648, .occ 651, .sumGe, .nonneg 20, .branchLe 39 (0), .branchLe 23 (0), .branchGe 6 (1), .branchGe 33 (1), .branchGe 12 (1), .branchGe 19 (1), .branchLe 22 (0)]

def plane487GenLeaf0037Mult : Fin 49 → Nat := ![26620, 3621, 62464, 31300, 16396, 19279, 47647, 16320, 10264, 9256, 36111, 9280, 602, 20709, 30760, 16766, 7778, 16340, 4588, 9862, 14731, 5147, 3115, 23015, 20056, 21662, 10238, 6309, 16010, 12400, 7572, 19773, 2572, 22982, 10821, 20159, 1263, 19066, 1456, 9441, 79253, 51411, 23712, 45567, 145569, 150062, 122098, 212517, 61885]

theorem plane487GenLeaf0037 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_33 : (1 : Int) ≤ x 33)
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0037Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0037Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0037Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0037Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 82
  · exact hroot.hOcc 83
  · exact hroot.hOcc 86
  · exact hroot.hOcc 92
  · exact hroot.hOcc 118
  · exact hroot.hOcc 119
  · exact hroot.hOcc 128
  · exact hroot.hOcc 148
  · exact hroot.hOcc 178
  · exact hroot.hOcc 206
  · exact hroot.hOcc 227
  · exact hroot.hOcc 230
  · exact hroot.hOcc 263
  · exact hroot.hOcc 296
  · exact hroot.hOcc 300
  · exact hroot.hOcc 303
  · exact hroot.hOcc 308
  · exact hroot.hOcc 312
  · exact hroot.hOcc 316
  · exact hroot.hOcc 322
  · exact hroot.hOcc 347
  · exact hroot.hOcc 352
  · exact hroot.hOcc 377
  · exact hroot.hOcc 378
  · exact hroot.hOcc 382
  · exact hroot.hOcc 386
  · exact hroot.hOcc 435
  · exact hroot.hOcc 446
  · exact hroot.hOcc 469
  · exact hroot.hOcc 470
  · exact hroot.hOcc 471
  · exact hroot.hOcc 490
  · exact hroot.hOcc 521
  · exact hroot.hOcc 529
  · exact hroot.hOcc 530
  · exact hroot.hOcc 546
  · exact hroot.hOcc 572
  · exact hroot.hOcc 633
  · exact hroot.hOcc 648
  · exact hroot.hOcc 651
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (20 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (6 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (33 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_33
  · change (∑ k, (if k = (12 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (19 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (22 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22

end QiushiMatmul
