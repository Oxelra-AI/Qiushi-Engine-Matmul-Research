import QiushiPlane471GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane471GenLeaf0003Refs : Fin 64 → RowRef 304 63 := ![.occ 2, .occ 3, .occ 7, .occ 31, .occ 46, .occ 72, .occ 82, .occ 85, .occ 93, .occ 95, .occ 108, .occ 110, .occ 111, .occ 114, .occ 118, .occ 119, .occ 128, .occ 135, .occ 140, .occ 143, .occ 144, .occ 150, .occ 160, .occ 162, .occ 167, .occ 175, .occ 176, .occ 178, .occ 187, .occ 201, .occ 204, .occ 207, .occ 213, .occ 221, .occ 241, .occ 248, .occ 250, .occ 256, .occ 258, .occ 273, .occ 284, .occ 286, .occ 300, .occ 302, .sumGe, .nonneg 17, .nonneg 21, .nonneg 26, .nonneg 27, .nonneg 34, .nonneg 37, .nonneg 42, .nonneg 47, .nonneg 49, .nonneg 51, .nonneg 52, .nonneg 53, .nonneg 55, .nonneg 58, .nonneg 61, .branchLe 48 (0), .branchLe 14 (0), .branchLe 38 (0), .branchGe 12 (1)]

def plane471GenLeaf0003Mult : Fin 64 → Nat := ![40620, 12148, 160262, 40454, 8018, 15352, 39572, 40068, 39400, 131765, 41866, 74, 41658, 1560, 13822, 56088, 10068, 11162, 1116, 90393, 10836, 21738, 2694, 33772, 5145, 317, 120919, 91407, 72338, 24157, 85286, 141, 22905, 13113, 3250, 89742, 866, 9084, 19154, 9825, 21558, 14747, 32200, 10788, 199166, 22570, 92936, 41922, 91468, 36176, 95832, 71804, 11728, 39482, 36252, 126050, 49110, 108938, 5804, 32198, 67558, 199166, 139032, 825740]

theorem plane471GenLeaf0003 (x : Fin 63 → Int)
    (hroot : plane471GenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hUB_48 : x 48 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_38 : x 38 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane471GenLeaf0003Refs i).resolveCoeff plane471GenOccSys j)
    (fun i => (plane471GenLeaf0003Refs i).resolveRhs plane471GenOccSys) plane471GenLeaf0003Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane471GenLeaf0003Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · exact hroot.hOcc 3
  · exact hroot.hOcc 7
  · exact hroot.hOcc 31
  · exact hroot.hOcc 46
  · exact hroot.hOcc 72
  · exact hroot.hOcc 82
  · exact hroot.hOcc 85
  · exact hroot.hOcc 93
  · exact hroot.hOcc 95
  · exact hroot.hOcc 108
  · exact hroot.hOcc 110
  · exact hroot.hOcc 111
  · exact hroot.hOcc 114
  · exact hroot.hOcc 118
  · exact hroot.hOcc 119
  · exact hroot.hOcc 128
  · exact hroot.hOcc 135
  · exact hroot.hOcc 140
  · exact hroot.hOcc 143
  · exact hroot.hOcc 144
  · exact hroot.hOcc 150
  · exact hroot.hOcc 160
  · exact hroot.hOcc 162
  · exact hroot.hOcc 167
  · exact hroot.hOcc 175
  · exact hroot.hOcc 176
  · exact hroot.hOcc 178
  · exact hroot.hOcc 187
  · exact hroot.hOcc 201
  · exact hroot.hOcc 204
  · exact hroot.hOcc 207
  · exact hroot.hOcc 213
  · exact hroot.hOcc 221
  · exact hroot.hOcc 241
  · exact hroot.hOcc 248
  · exact hroot.hOcc 250
  · exact hroot.hOcc 256
  · exact hroot.hOcc 258
  · exact hroot.hOcc 273
  · exact hroot.hOcc 284
  · exact hroot.hOcc 286
  · exact hroot.hOcc 300
  · exact hroot.hOcc 302
  · change (∑ j, (-1 : Int) * x j) ≤ -plane471GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (17 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (21 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (26 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (27 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27
  · change (∑ k, (if k = (34 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 34
  · change (∑ k, (if k = (37 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (42 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (47 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (49 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (51 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 51
  · change (∑ k, (if k = (52 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (53 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (55 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (58 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 58
  · change (∑ k, (if k = (61 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 61
  · change (∑ k, (if k = (48 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_48
  · change (∑ k, (if k = (14 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (38 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (12 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12

end QiushiMatmul
