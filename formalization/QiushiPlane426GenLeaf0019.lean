import QiushiPlane426GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane426GenLeaf0019Refs : Fin 59 → RowRef 340 58 := ![.occ 5, .occ 33, .occ 34, .occ 78, .occ 81, .occ 84, .occ 88, .occ 99, .occ 101, .occ 102, .occ 103, .occ 109, .occ 113, .occ 116, .occ 121, .occ 123, .occ 128, .occ 131, .occ 140, .occ 151, .occ 155, .occ 170, .occ 179, .occ 205, .occ 232, .occ 235, .occ 250, .occ 251, .occ 252, .occ 260, .occ 279, .occ 280, .occ 299, .occ 318, .occ 320, .occ 323, .occ 334, .occ 337, .occ 338, .sumGe, .nonneg 6, .nonneg 16, .nonneg 17, .nonneg 25, .nonneg 28, .nonneg 30, .nonneg 33, .nonneg 38, .nonneg 39, .nonneg 47, .nonneg 50, .branchLe 43 (0), .branchGe 14 (1), .branchLe 42 (0), .branchLe 18 (0), .branchLe 56 (0), .branchLe 11 (0), .branchLe 51 (0), .branchGe 49 (1)]

def plane426GenLeaf0019Mult : Fin 59 → Nat := ![25470, 5166, 16670, 14658, 3306, 26382, 5892, 1768, 2834, 17104, 17324, 27264, 14580, 16938, 10980, 6412, 29080, 2746, 3652, 7212, 1822, 2200, 5398, 4746, 13410, 1500, 8585, 2506, 11438, 3713, 5252, 14230, 9460, 3226, 923, 1272, 12524, 715, 6160, 51698, 2168, 51226, 49372, 2234, 4062, 6776, 21304, 8816, 800, 16230, 5710, 34806, 83492, 18010, 39174, 47270, 30242, 50426, 123288]

theorem plane426GenLeaf0019 (x : Fin 58 → Int)
    (hroot : plane426GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_49 : (1 : Int) ≤ x 49)
    (hUB_43 : x 43 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_56 : x 56 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_51 : x 51 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane426GenLeaf0019Refs i).resolveCoeff plane426GenOccSys j)
    (fun i => (plane426GenLeaf0019Refs i).resolveRhs plane426GenOccSys) plane426GenLeaf0019Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane426GenLeaf0019Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · exact hroot.hOcc 33
  · exact hroot.hOcc 34
  · exact hroot.hOcc 78
  · exact hroot.hOcc 81
  · exact hroot.hOcc 84
  · exact hroot.hOcc 88
  · exact hroot.hOcc 99
  · exact hroot.hOcc 101
  · exact hroot.hOcc 102
  · exact hroot.hOcc 103
  · exact hroot.hOcc 109
  · exact hroot.hOcc 113
  · exact hroot.hOcc 116
  · exact hroot.hOcc 121
  · exact hroot.hOcc 123
  · exact hroot.hOcc 128
  · exact hroot.hOcc 131
  · exact hroot.hOcc 140
  · exact hroot.hOcc 151
  · exact hroot.hOcc 155
  · exact hroot.hOcc 170
  · exact hroot.hOcc 179
  · exact hroot.hOcc 205
  · exact hroot.hOcc 232
  · exact hroot.hOcc 235
  · exact hroot.hOcc 250
  · exact hroot.hOcc 251
  · exact hroot.hOcc 252
  · exact hroot.hOcc 260
  · exact hroot.hOcc 279
  · exact hroot.hOcc 280
  · exact hroot.hOcc 299
  · exact hroot.hOcc 318
  · exact hroot.hOcc 320
  · exact hroot.hOcc 323
  · exact hroot.hOcc 334
  · exact hroot.hOcc 337
  · exact hroot.hOcc 338
  · change (∑ j, (-1 : Int) * x j) ≤ -plane426GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (16 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (25 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (28 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (30 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (33 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (38 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (39 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (47 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (50 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (43 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (14 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (42 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (18 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (56 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_56
  · change (∑ k, (if k = (11 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (51 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_51
  · change (∑ k, (if k = (49 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_49

end QiushiMatmul
