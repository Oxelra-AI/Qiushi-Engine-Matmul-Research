import QiushiPlane471GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane471GenLeaf0007Refs : Fin 64 → RowRef 304 63 := ![.occ 2, .occ 9, .occ 17, .occ 19, .occ 28, .occ 30, .occ 31, .occ 44, .occ 50, .occ 57, .occ 62, .occ 67, .occ 82, .occ 83, .occ 86, .occ 95, .occ 96, .occ 108, .occ 109, .occ 111, .occ 112, .occ 118, .occ 131, .occ 134, .occ 138, .occ 152, .occ 159, .occ 192, .occ 201, .occ 202, .occ 203, .occ 220, .occ 224, .occ 225, .occ 226, .occ 227, .occ 233, .occ 234, .occ 240, .occ 241, .occ 249, .occ 269, .occ 272, .occ 290, .occ 291, .occ 295, .occ 297, .sumGe, .nonneg 3, .nonneg 15, .nonneg 17, .nonneg 21, .nonneg 30, .nonneg 34, .nonneg 39, .nonneg 41, .nonneg 44, .nonneg 49, .nonneg 62, .branchLe 48 (0), .branchGe 14 (1), .branchLe 4 (0), .branchLe 38 (0), .branchGe 19 (1)]

def plane471GenLeaf0007Mult : Fin 64 → Nat := ![28952, 54278, 4038, 23592, 10682, 20619, 33087, 2873, 4301, 13772, 5247, 97193, 50825, 85166, 26634, 10129, 12281, 70396, 4867, 2741, 44374, 42651, 10395, 360, 7273, 52864, 17148, 9406, 9919, 1611, 13764, 7539, 4568, 31981, 19014, 29139, 22639, 4060, 19820, 69714, 201, 7528, 7932, 2273, 2061, 5654, 21894, 128282, 13363, 17914, 9312, 20806, 36146, 28664, 19124, 16255, 22919, 41511, 10032, 53019, 49450, 102054, 76994, 591766]

theorem plane471GenLeaf0007 (x : Fin 63 → Int)
    (hroot : plane471GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hUB_48 : x 48 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_38 : x 38 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane471GenLeaf0007Refs i).resolveCoeff plane471GenOccSys j)
    (fun i => (plane471GenLeaf0007Refs i).resolveRhs plane471GenOccSys) plane471GenLeaf0007Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane471GenLeaf0007Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · exact hroot.hOcc 9
  · exact hroot.hOcc 17
  · exact hroot.hOcc 19
  · exact hroot.hOcc 28
  · exact hroot.hOcc 30
  · exact hroot.hOcc 31
  · exact hroot.hOcc 44
  · exact hroot.hOcc 50
  · exact hroot.hOcc 57
  · exact hroot.hOcc 62
  · exact hroot.hOcc 67
  · exact hroot.hOcc 82
  · exact hroot.hOcc 83
  · exact hroot.hOcc 86
  · exact hroot.hOcc 95
  · exact hroot.hOcc 96
  · exact hroot.hOcc 108
  · exact hroot.hOcc 109
  · exact hroot.hOcc 111
  · exact hroot.hOcc 112
  · exact hroot.hOcc 118
  · exact hroot.hOcc 131
  · exact hroot.hOcc 134
  · exact hroot.hOcc 138
  · exact hroot.hOcc 152
  · exact hroot.hOcc 159
  · exact hroot.hOcc 192
  · exact hroot.hOcc 201
  · exact hroot.hOcc 202
  · exact hroot.hOcc 203
  · exact hroot.hOcc 220
  · exact hroot.hOcc 224
  · exact hroot.hOcc 225
  · exact hroot.hOcc 226
  · exact hroot.hOcc 227
  · exact hroot.hOcc 233
  · exact hroot.hOcc 234
  · exact hroot.hOcc 240
  · exact hroot.hOcc 241
  · exact hroot.hOcc 249
  · exact hroot.hOcc 269
  · exact hroot.hOcc 272
  · exact hroot.hOcc 290
  · exact hroot.hOcc 291
  · exact hroot.hOcc 295
  · exact hroot.hOcc 297
  · change (∑ j, (-1 : Int) * x j) ≤ -plane471GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (15 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (17 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (21 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (30 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (34 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 34
  · change (∑ k, (if k = (39 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (41 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (44 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (49 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (62 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 62
  · change (∑ k, (if k = (48 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_48
  · change (∑ k, (if k = (14 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (4 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (38 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (19 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19

end QiushiMatmul
