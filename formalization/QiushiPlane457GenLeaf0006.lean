import QiushiPlane457GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane457GenLeaf0006Refs : Fin 49 → RowRef 178 49 := ![.occ 18, .occ 21, .occ 22, .occ 23, .occ 24, .occ 27, .occ 33, .occ 42, .occ 43, .occ 45, .occ 50, .occ 59, .occ 64, .occ 67, .occ 68, .occ 69, .occ 71, .occ 72, .occ 75, .occ 77, .occ 82, .occ 91, .occ 97, .occ 98, .occ 109, .occ 115, .occ 118, .occ 123, .occ 133, .occ 134, .occ 136, .occ 137, .occ 141, .occ 148, .occ 155, .occ 156, .occ 157, .occ 161, .occ 174, .sumGe, .nonneg 6, .nonneg 8, .nonneg 27, .nonneg 32, .nonneg 33, .nonneg 39, .nonneg 40, .branchGe 3 (1), .branchGe 23 (1)]

def plane457GenLeaf0006Mult : Fin 49 → Nat := ![1713, 2456, 2460, 2570, 209, 1416, 1813, 5237, 2634, 1593, 762, 12, 454, 3290, 12, 4239, 637, 1450, 2223, 554, 5225, 1396, 1501, 2941, 147, 1062, 1096, 998, 210, 986, 124, 2448, 673, 954, 976, 1681, 110, 615, 12, 5237, 1749, 2, 3241, 1384, 1723, 2553, 1108, 14720, 22577]

theorem plane457GenLeaf0006 (x : Fin 49 → Int)
    (hroot : plane457GenOccSys.RootHolds x)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_23 : (1 : Int) ≤ x 23)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane457GenLeaf0006Refs i).resolveCoeff plane457GenOccSys j)
    (fun i => (plane457GenLeaf0006Refs i).resolveRhs plane457GenOccSys) plane457GenLeaf0006Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane457GenLeaf0006Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 18
  · exact hroot.hOcc 21
  · exact hroot.hOcc 22
  · exact hroot.hOcc 23
  · exact hroot.hOcc 24
  · exact hroot.hOcc 27
  · exact hroot.hOcc 33
  · exact hroot.hOcc 42
  · exact hroot.hOcc 43
  · exact hroot.hOcc 45
  · exact hroot.hOcc 50
  · exact hroot.hOcc 59
  · exact hroot.hOcc 64
  · exact hroot.hOcc 67
  · exact hroot.hOcc 68
  · exact hroot.hOcc 69
  · exact hroot.hOcc 71
  · exact hroot.hOcc 72
  · exact hroot.hOcc 75
  · exact hroot.hOcc 77
  · exact hroot.hOcc 82
  · exact hroot.hOcc 91
  · exact hroot.hOcc 97
  · exact hroot.hOcc 98
  · exact hroot.hOcc 109
  · exact hroot.hOcc 115
  · exact hroot.hOcc 118
  · exact hroot.hOcc 123
  · exact hroot.hOcc 133
  · exact hroot.hOcc 134
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 141
  · exact hroot.hOcc 148
  · exact hroot.hOcc 155
  · exact hroot.hOcc 156
  · exact hroot.hOcc 157
  · exact hroot.hOcc 161
  · exact hroot.hOcc 174
  · change (∑ j, (-1 : Int) * x j) ≤ -plane457GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (8 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (27 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27
  · change (∑ k, (if k = (32 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (33 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (39 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (40 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (3 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3
  · change (∑ k, (if k = (23 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23

end QiushiMatmul
