import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0006Refs : Fin 49 → RowRef 668 48 := ![.occ 89, .occ 102, .occ 106, .occ 126, .occ 151, .occ 152, .occ 171, .occ 178, .occ 184, .occ 187, .occ 203, .occ 210, .occ 217, .occ 223, .occ 231, .occ 246, .occ 257, .occ 263, .occ 269, .occ 275, .occ 315, .occ 347, .occ 350, .occ 356, .occ 380, .occ 381, .occ 386, .occ 389, .occ 399, .occ 539, .occ 546, .occ 572, .occ 577, .occ 586, .occ 608, .occ 609, .occ 639, .occ 651, .occ 664, .sumGe, .branchLe 39 (0), .branchLe 23 (0), .branchLe 6 (0), .branchLe 25 (0), .branchLe 12 (0), .branchLe 15 (0), .branchGe 16 (1), .branchLe 14 (0), .branchGe 33 (1)]

def plane487GenLeaf0006Mult : Fin 49 → Nat := ![32096, 24475, 3091, 835, 11357, 5218, 1514, 1717, 6859, 3373, 18029, 3347, 14660, 16586, 10293, 19775, 8314, 10185, 7514, 100, 6101, 15217, 15230, 12959, 10331, 9489, 5473, 8018, 16898, 13498, 11445, 3113, 2340, 3560, 5866, 4901, 4276, 1402, 1170, 50164, 37549, 25950, 50164, 33266, 43316, 9671, 93454, 26129, 75208]

theorem plane487GenLeaf0006 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_33 : (1 : Int) ≤ x 33)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0006Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0006Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0006Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0006Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 89
  · exact hroot.hOcc 102
  · exact hroot.hOcc 106
  · exact hroot.hOcc 126
  · exact hroot.hOcc 151
  · exact hroot.hOcc 152
  · exact hroot.hOcc 171
  · exact hroot.hOcc 178
  · exact hroot.hOcc 184
  · exact hroot.hOcc 187
  · exact hroot.hOcc 203
  · exact hroot.hOcc 210
  · exact hroot.hOcc 217
  · exact hroot.hOcc 223
  · exact hroot.hOcc 231
  · exact hroot.hOcc 246
  · exact hroot.hOcc 257
  · exact hroot.hOcc 263
  · exact hroot.hOcc 269
  · exact hroot.hOcc 275
  · exact hroot.hOcc 315
  · exact hroot.hOcc 347
  · exact hroot.hOcc 350
  · exact hroot.hOcc 356
  · exact hroot.hOcc 380
  · exact hroot.hOcc 381
  · exact hroot.hOcc 386
  · exact hroot.hOcc 389
  · exact hroot.hOcc 399
  · exact hroot.hOcc 539
  · exact hroot.hOcc 546
  · exact hroot.hOcc 572
  · exact hroot.hOcc 577
  · exact hroot.hOcc 586
  · exact hroot.hOcc 608
  · exact hroot.hOcc 609
  · exact hroot.hOcc 639
  · exact hroot.hOcc 651
  · exact hroot.hOcc 664
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (6 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (25 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (12 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (15 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (16 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (14 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (33 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_33

end QiushiMatmul
