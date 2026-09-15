import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0077Refs : Fin 49 → RowRef 668 48 := ![.occ 83, .occ 94, .occ 100, .occ 105, .occ 147, .occ 160, .occ 161, .occ 174, .occ 177, .occ 219, .occ 235, .occ 237, .occ 239, .occ 246, .occ 284, .occ 294, .occ 296, .occ 302, .occ 303, .occ 305, .occ 315, .occ 332, .occ 378, .occ 386, .occ 401, .occ 452, .occ 482, .occ 498, .occ 502, .occ 505, .occ 532, .occ 534, .occ 544, .occ 546, .occ 660, .occ 661, .occ 662, .occ 665, .sumGe, .nonneg 8, .branchGe 39 (1), .branchLe 7 (0), .branchGe 28 (1), .branchLe 3 (0), .branchLe 36 (0), .branchLe 35 (0), .branchLe 13 (0), .branchLe 37 (0), .branchLe 38 (0)]

def plane487GenLeaf0077Mult : Fin 49 → Nat := ![23429, 4582, 27322, 31485, 39122, 1522, 7295, 36491, 19623, 697, 3188, 28895, 9084, 376, 2292, 9056, 925, 1442, 2661, 22062, 6978, 16610, 2011, 4829, 31128, 3475, 4402, 291, 805, 3790, 3175, 3306, 10740, 2661, 4758, 6542, 10404, 20051, 56365, 25946, 87405, 16941, 195322, 45961, 42508, 34926, 28679, 22353, 33614]

theorem plane487GenLeaf0077 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_38 : x 38 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0077Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0077Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0077Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0077Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 83
  · exact hroot.hOcc 94
  · exact hroot.hOcc 100
  · exact hroot.hOcc 105
  · exact hroot.hOcc 147
  · exact hroot.hOcc 160
  · exact hroot.hOcc 161
  · exact hroot.hOcc 174
  · exact hroot.hOcc 177
  · exact hroot.hOcc 219
  · exact hroot.hOcc 235
  · exact hroot.hOcc 237
  · exact hroot.hOcc 239
  · exact hroot.hOcc 246
  · exact hroot.hOcc 284
  · exact hroot.hOcc 294
  · exact hroot.hOcc 296
  · exact hroot.hOcc 302
  · exact hroot.hOcc 303
  · exact hroot.hOcc 305
  · exact hroot.hOcc 315
  · exact hroot.hOcc 332
  · exact hroot.hOcc 378
  · exact hroot.hOcc 386
  · exact hroot.hOcc 401
  · exact hroot.hOcc 452
  · exact hroot.hOcc 482
  · exact hroot.hOcc 498
  · exact hroot.hOcc 502
  · exact hroot.hOcc 505
  · exact hroot.hOcc 532
  · exact hroot.hOcc 534
  · exact hroot.hOcc 544
  · exact hroot.hOcc 546
  · exact hroot.hOcc 660
  · exact hroot.hOcc 661
  · exact hroot.hOcc 662
  · exact hroot.hOcc 665
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (39 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (7 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (28 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (3 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (36 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (35 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (13 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (37 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (38 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38

end QiushiMatmul
