import QiushiPlane463GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane463GenLeaf0011Refs : Fin 64 → RowRef 278 63 := ![.occ 2, .occ 3, .occ 5, .occ 9, .occ 10, .occ 11, .occ 14, .occ 29, .occ 30, .occ 46, .occ 54, .occ 57, .occ 62, .occ 79, .occ 102, .occ 105, .occ 109, .occ 124, .occ 132, .occ 135, .occ 141, .occ 146, .occ 148, .occ 150, .occ 154, .occ 169, .occ 178, .occ 195, .occ 203, .occ 225, .occ 226, .occ 242, .occ 246, .occ 250, .occ 252, .occ 256, .occ 266, .occ 267, .occ 269, .occ 270, .occ 271, .occ 272, .occ 273, .sumGe, .nonneg 0, .nonneg 10, .nonneg 12, .nonneg 13, .nonneg 14, .nonneg 37, .nonneg 38, .nonneg 39, .nonneg 40, .nonneg 41, .nonneg 43, .nonneg 48, .nonneg 52, .nonneg 54, .nonneg 57, .nonneg 59, .nonneg 61, .branchGe 15 (1), .branchLe 23 (0), .branchLe 33 (0)]

def plane463GenLeaf0011Mult : Fin 64 → Nat := ![33948, 88848, 10286, 111514, 151766, 297324, 60934, 128836, 4116, 511456, 444856, 81468, 38004, 272948, 31838, 299142, 134696, 117474, 226038, 85740, 187850, 109212, 15766, 103300, 66788, 153228, 24304, 4174, 6066, 14608, 71618, 111402, 233488, 77792, 31466, 65076, 65076, 141740, 95345, 17553, 13733, 63299, 93748, 592662, 364908, 382472, 29724, 56068, 156502, 113078, 136828, 348888, 77140, 421994, 181772, 59810, 172268, 77144, 868270, 279084, 145476, 2768266, 462910, 483584]

theorem plane463GenLeaf0011 (x : Fin 63 → Int)
    (hroot : plane463GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane463GenLeaf0011Refs i).resolveCoeff plane463GenOccSys j)
    (fun i => (plane463GenLeaf0011Refs i).resolveRhs plane463GenOccSys) plane463GenLeaf0011Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane463GenLeaf0011Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · exact hroot.hOcc 3
  · exact hroot.hOcc 5
  · exact hroot.hOcc 9
  · exact hroot.hOcc 10
  · exact hroot.hOcc 11
  · exact hroot.hOcc 14
  · exact hroot.hOcc 29
  · exact hroot.hOcc 30
  · exact hroot.hOcc 46
  · exact hroot.hOcc 54
  · exact hroot.hOcc 57
  · exact hroot.hOcc 62
  · exact hroot.hOcc 79
  · exact hroot.hOcc 102
  · exact hroot.hOcc 105
  · exact hroot.hOcc 109
  · exact hroot.hOcc 124
  · exact hroot.hOcc 132
  · exact hroot.hOcc 135
  · exact hroot.hOcc 141
  · exact hroot.hOcc 146
  · exact hroot.hOcc 148
  · exact hroot.hOcc 150
  · exact hroot.hOcc 154
  · exact hroot.hOcc 169
  · exact hroot.hOcc 178
  · exact hroot.hOcc 195
  · exact hroot.hOcc 203
  · exact hroot.hOcc 225
  · exact hroot.hOcc 226
  · exact hroot.hOcc 242
  · exact hroot.hOcc 246
  · exact hroot.hOcc 250
  · exact hroot.hOcc 252
  · exact hroot.hOcc 256
  · exact hroot.hOcc 266
  · exact hroot.hOcc 267
  · exact hroot.hOcc 269
  · exact hroot.hOcc 270
  · exact hroot.hOcc 271
  · exact hroot.hOcc 272
  · exact hroot.hOcc 273
  · change (∑ j, (-1 : Int) * x j) ≤ -plane463GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (10 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (12 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (13 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (14 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (37 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (38 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (39 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (40 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (41 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (43 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 43
  · change (∑ k, (if k = (48 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (52 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (54 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 54
  · change (∑ k, (if k = (57 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 57
  · change (∑ k, (if k = (59 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (61 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 61
  · change (∑ k, (if k = (15 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (23 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (33 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33

end QiushiMatmul
