import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0066Refs : Fin 49 → RowRef 668 48 := ![.occ 94, .occ 99, .occ 103, .occ 106, .occ 128, .occ 129, .occ 130, .occ 157, .occ 161, .occ 162, .occ 191, .occ 198, .occ 201, .occ 218, .occ 219, .occ 227, .occ 246, .occ 256, .occ 258, .occ 281, .occ 288, .occ 303, .occ 313, .occ 314, .occ 315, .occ 334, .occ 343, .occ 348, .occ 351, .occ 381, .occ 401, .occ 402, .occ 413, .occ 429, .occ 450, .occ 509, .occ 526, .occ 536, .occ 604, .occ 653, .occ 657, .sumGe, .branchGe 39 (1), .branchLe 7 (0), .branchLe 28 (0), .branchLe 40 (0), .branchLe 29 (0), .branchGe 19 (1), .branchGe 17 (1)]

def plane487GenLeaf0066Mult : Fin 49 → Nat := ![5701, 5105, 4319, 49058, 12406, 59404, 4258, 4819, 39158, 26047, 21921, 8732, 28280, 24174, 6049, 20873, 2346, 1327, 13965, 26945, 4768, 11049, 4706, 8897, 10756, 21545, 29717, 9676, 4477, 11277, 9790, 12209, 19449, 1092, 931, 7360, 14287, 2742, 6146, 10611, 9239, 60335, 146668, 13571, 57593, 33969, 48126, 171032, 207834]

theorem plane487GenLeaf0066 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0066Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0066Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0066Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0066Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 94
  · exact hroot.hOcc 99
  · exact hroot.hOcc 103
  · exact hroot.hOcc 106
  · exact hroot.hOcc 128
  · exact hroot.hOcc 129
  · exact hroot.hOcc 130
  · exact hroot.hOcc 157
  · exact hroot.hOcc 161
  · exact hroot.hOcc 162
  · exact hroot.hOcc 191
  · exact hroot.hOcc 198
  · exact hroot.hOcc 201
  · exact hroot.hOcc 218
  · exact hroot.hOcc 219
  · exact hroot.hOcc 227
  · exact hroot.hOcc 246
  · exact hroot.hOcc 256
  · exact hroot.hOcc 258
  · exact hroot.hOcc 281
  · exact hroot.hOcc 288
  · exact hroot.hOcc 303
  · exact hroot.hOcc 313
  · exact hroot.hOcc 314
  · exact hroot.hOcc 315
  · exact hroot.hOcc 334
  · exact hroot.hOcc 343
  · exact hroot.hOcc 348
  · exact hroot.hOcc 351
  · exact hroot.hOcc 381
  · exact hroot.hOcc 401
  · exact hroot.hOcc 402
  · exact hroot.hOcc 413
  · exact hroot.hOcc 429
  · exact hroot.hOcc 450
  · exact hroot.hOcc 509
  · exact hroot.hOcc 526
  · exact hroot.hOcc 536
  · exact hroot.hOcc 604
  · exact hroot.hOcc 653
  · exact hroot.hOcc 657
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (39 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (7 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (28 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (40 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (29 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (19 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (17 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17

end QiushiMatmul
