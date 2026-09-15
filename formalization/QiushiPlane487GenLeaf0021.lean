import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0021Refs : Fin 49 → RowRef 668 48 := ![.occ 82, .occ 86, .occ 94, .occ 102, .occ 110, .occ 117, .occ 118, .occ 119, .occ 120, .occ 186, .occ 218, .occ 224, .occ 227, .occ 231, .occ 253, .occ 294, .occ 295, .occ 303, .occ 308, .occ 360, .occ 369, .occ 386, .occ 394, .occ 400, .occ 404, .occ 415, .occ 431, .occ 461, .occ 462, .occ 468, .occ 471, .occ 500, .occ 598, .occ 608, .occ 634, .occ 648, .occ 651, .sumGe, .nonneg 0, .branchLe 39 (0), .branchLe 23 (0), .branchGe 6 (1), .branchLe 33 (0), .branchLe 14 (0), .branchLe 29 (0), .branchLe 44 (0), .branchLe 25 (0), .branchLe 22 (0), .branchLe 41 (0)]

def plane487GenLeaf0021Mult : Fin 49 → Nat := ![48428, 557, 631, 10790, 33775, 4869, 14946, 8824, 27581, 23715, 2210, 15338, 11458, 23374, 28334, 19660, 27772, 10424, 17456, 8931, 727, 32144, 3168, 16541, 8801, 11101, 6982, 2541, 4906, 5821, 19002, 9412, 7321, 3280, 7274, 18102, 10409, 82198, 3173, 74877, 71789, 170210, 82198, 52108, 53687, 47152, 51869, 69233, 45094]

theorem plane487GenLeaf0021 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hUB_41 : x 41 ≤ (0 : Int))
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0021Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0021Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0021Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0021Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 82
  · exact hroot.hOcc 86
  · exact hroot.hOcc 94
  · exact hroot.hOcc 102
  · exact hroot.hOcc 110
  · exact hroot.hOcc 117
  · exact hroot.hOcc 118
  · exact hroot.hOcc 119
  · exact hroot.hOcc 120
  · exact hroot.hOcc 186
  · exact hroot.hOcc 218
  · exact hroot.hOcc 224
  · exact hroot.hOcc 227
  · exact hroot.hOcc 231
  · exact hroot.hOcc 253
  · exact hroot.hOcc 294
  · exact hroot.hOcc 295
  · exact hroot.hOcc 303
  · exact hroot.hOcc 308
  · exact hroot.hOcc 360
  · exact hroot.hOcc 369
  · exact hroot.hOcc 386
  · exact hroot.hOcc 394
  · exact hroot.hOcc 400
  · exact hroot.hOcc 404
  · exact hroot.hOcc 415
  · exact hroot.hOcc 431
  · exact hroot.hOcc 461
  · exact hroot.hOcc 462
  · exact hroot.hOcc 468
  · exact hroot.hOcc 471
  · exact hroot.hOcc 500
  · exact hroot.hOcc 598
  · exact hroot.hOcc 608
  · exact hroot.hOcc 634
  · exact hroot.hOcc 648
  · exact hroot.hOcc 651
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (6 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (33 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (14 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (29 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (44 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (25 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (22 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (41 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_41

end QiushiMatmul
