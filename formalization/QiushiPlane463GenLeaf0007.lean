import QiushiPlane463GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane463GenLeaf0007Refs : Fin 64 → RowRef 278 63 := ![.occ 7, .occ 12, .occ 13, .occ 14, .occ 25, .occ 28, .occ 32, .occ 48, .occ 49, .occ 59, .occ 65, .occ 69, .occ 71, .occ 76, .occ 79, .occ 90, .occ 103, .occ 114, .occ 121, .occ 147, .occ 153, .occ 154, .occ 157, .occ 158, .occ 168, .occ 170, .occ 174, .occ 175, .occ 199, .occ 200, .occ 211, .occ 218, .occ 222, .occ 225, .occ 236, .occ 237, .occ 238, .occ 243, .occ 253, .occ 264, .occ 265, .occ 266, .occ 270, .occ 273, .occ 274, .sumGe, .nonneg 0, .nonneg 10, .nonneg 12, .nonneg 13, .nonneg 14, .nonneg 37, .nonneg 44, .nonneg 48, .nonneg 54, .nonneg 56, .nonneg 57, .nonneg 59, .nonneg 61, .branchLe 15 (0), .branchLe 24 (0), .branchLe 60 (0), .branchGe 21 (1), .branchLe 35 (0)]

def plane463GenLeaf0007Mult : Fin 64 → Nat := ![64760, 56411, 8933, 49157, 22284, 142243, 21537, 12082, 21465, 54011, 78732, 64735, 22982, 4802, 84151, 11058, 68999, 42755, 13787, 17687, 88827, 10064, 19880, 1717, 50572, 45799, 38588, 42057, 5645, 496, 28078, 12085, 20036, 25908, 31143, 967, 9910, 22431, 41202, 41973, 899, 30016, 2103, 1465, 4532, 173323, 125362, 188556, 6141, 40978, 10454, 141831, 21523, 80689, 96773, 94731, 102290, 124995, 91005, 168791, 79212, 51765, 600775, 146652]

theorem plane463GenLeaf0007 (x : Fin 63 → Int)
    (hroot : plane463GenOccSys.RootHolds x)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_60 : x 60 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane463GenLeaf0007Refs i).resolveCoeff plane463GenOccSys j)
    (fun i => (plane463GenLeaf0007Refs i).resolveRhs plane463GenOccSys) plane463GenLeaf0007Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane463GenLeaf0007Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 7
  · exact hroot.hOcc 12
  · exact hroot.hOcc 13
  · exact hroot.hOcc 14
  · exact hroot.hOcc 25
  · exact hroot.hOcc 28
  · exact hroot.hOcc 32
  · exact hroot.hOcc 48
  · exact hroot.hOcc 49
  · exact hroot.hOcc 59
  · exact hroot.hOcc 65
  · exact hroot.hOcc 69
  · exact hroot.hOcc 71
  · exact hroot.hOcc 76
  · exact hroot.hOcc 79
  · exact hroot.hOcc 90
  · exact hroot.hOcc 103
  · exact hroot.hOcc 114
  · exact hroot.hOcc 121
  · exact hroot.hOcc 147
  · exact hroot.hOcc 153
  · exact hroot.hOcc 154
  · exact hroot.hOcc 157
  · exact hroot.hOcc 158
  · exact hroot.hOcc 168
  · exact hroot.hOcc 170
  · exact hroot.hOcc 174
  · exact hroot.hOcc 175
  · exact hroot.hOcc 199
  · exact hroot.hOcc 200
  · exact hroot.hOcc 211
  · exact hroot.hOcc 218
  · exact hroot.hOcc 222
  · exact hroot.hOcc 225
  · exact hroot.hOcc 236
  · exact hroot.hOcc 237
  · exact hroot.hOcc 238
  · exact hroot.hOcc 243
  · exact hroot.hOcc 253
  · exact hroot.hOcc 264
  · exact hroot.hOcc 265
  · exact hroot.hOcc 266
  · exact hroot.hOcc 270
  · exact hroot.hOcc 273
  · exact hroot.hOcc 274
  · change (∑ j, (-1 : Int) * x j) ≤ -plane463GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (10 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (12 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (13 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (14 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (37 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (44 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (48 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (54 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 54
  · change (∑ k, (if k = (56 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 56
  · change (∑ k, (if k = (57 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 57
  · change (∑ k, (if k = (59 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (61 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 61
  · change (∑ k, (if k = (15 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (24 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (60 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_60
  · change (∑ k, (if k = (21 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21
  · change (∑ k, (if k = (35 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35

end QiushiMatmul
