import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0008Refs : Fin 49 → RowRef 668 48 := ![.occ 83, .occ 85, .occ 87, .occ 95, .occ 100, .occ 101, .occ 105, .occ 132, .occ 158, .occ 171, .occ 214, .occ 216, .occ 217, .occ 221, .occ 225, .occ 240, .occ 246, .occ 253, .occ 256, .occ 269, .occ 276, .occ 297, .occ 303, .occ 308, .occ 315, .occ 347, .occ 353, .occ 381, .occ 399, .occ 403, .occ 407, .occ 412, .occ 455, .occ 501, .occ 514, .occ 521, .occ 536, .occ 629, .occ 662, .sumGe, .nonneg 7, .nonneg 8, .branchLe 39 (0), .branchLe 23 (0), .branchLe 6 (0), .branchLe 25 (0), .branchLe 12 (0), .branchGe 15 (1), .branchLe 40 (0)]

def plane487GenLeaf0008Mult : Fin 49 → Nat := ![3030, 2288, 1208, 2188, 951, 2728, 413, 2770, 2266, 558, 5722, 3075, 2294, 2477, 1041, 638, 866, 774, 904, 1060, 152, 601, 1409, 1631, 3708, 615, 1402, 651, 1947, 873, 255, 1784, 17, 940, 1294, 261, 2042, 530, 651, 7316, 1363, 1795, 6665, 3078, 7316, 5108, 7316, 25338, 5907]

theorem plane487GenLeaf0008 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0008Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0008Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0008Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0008Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 83
  · exact hroot.hOcc 85
  · exact hroot.hOcc 87
  · exact hroot.hOcc 95
  · exact hroot.hOcc 100
  · exact hroot.hOcc 101
  · exact hroot.hOcc 105
  · exact hroot.hOcc 132
  · exact hroot.hOcc 158
  · exact hroot.hOcc 171
  · exact hroot.hOcc 214
  · exact hroot.hOcc 216
  · exact hroot.hOcc 217
  · exact hroot.hOcc 221
  · exact hroot.hOcc 225
  · exact hroot.hOcc 240
  · exact hroot.hOcc 246
  · exact hroot.hOcc 253
  · exact hroot.hOcc 256
  · exact hroot.hOcc 269
  · exact hroot.hOcc 276
  · exact hroot.hOcc 297
  · exact hroot.hOcc 303
  · exact hroot.hOcc 308
  · exact hroot.hOcc 315
  · exact hroot.hOcc 347
  · exact hroot.hOcc 353
  · exact hroot.hOcc 381
  · exact hroot.hOcc 399
  · exact hroot.hOcc 403
  · exact hroot.hOcc 407
  · exact hroot.hOcc 412
  · exact hroot.hOcc 455
  · exact hroot.hOcc 501
  · exact hroot.hOcc 514
  · exact hroot.hOcc 521
  · exact hroot.hOcc 536
  · exact hroot.hOcc 629
  · exact hroot.hOcc 662
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (8 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (6 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (25 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (12 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (15 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (40 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40

end QiushiMatmul
