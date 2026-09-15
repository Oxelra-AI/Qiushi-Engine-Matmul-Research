import QiushiPlane470GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane470GenLeaf0003Refs : Fin 64 → RowRef 232 63 := ![.occ 7, .occ 9, .occ 12, .occ 14, .occ 15, .occ 19, .occ 21, .occ 32, .occ 39, .occ 42, .occ 43, .occ 65, .occ 71, .occ 72, .occ 74, .occ 78, .occ 80, .occ 82, .occ 88, .occ 91, .occ 92, .occ 96, .occ 103, .occ 106, .occ 108, .occ 112, .occ 123, .occ 126, .occ 127, .occ 129, .occ 144, .occ 149, .occ 160, .occ 162, .occ 165, .occ 168, .occ 169, .occ 179, .occ 183, .occ 187, .occ 192, .occ 197, .occ 199, .occ 201, .occ 216, .occ 222, .sumGe, .nonneg 3, .nonneg 21, .nonneg 24, .nonneg 32, .nonneg 45, .nonneg 47, .nonneg 48, .nonneg 50, .nonneg 55, .nonneg 56, .nonneg 59, .nonneg 62, .branchLe 12 (0), .branchLe 60 (0), .branchLe 25 (0), .branchLe 15 (0), .branchGe 4 (1)]

def plane470GenLeaf0003Mult : Fin 64 → Nat := ![25174, 34282, 12728, 47362, 20635, 14717, 25186, 17469, 14964, 12533, 1826, 27954, 16127, 1826, 26861, 26753, 14082, 24569, 6600, 768, 1442, 16196, 24832, 29020, 8256, 5886, 3702, 18192, 21350, 170, 5762, 11823, 688, 9244, 3968, 3619, 150, 4138, 7119, 5090, 231, 5106, 2328, 6478, 2078, 6167, 47362, 4576, 7826, 20068, 79990, 35536, 4418, 9180, 7058, 30458, 3389, 9027, 27840, 40378, 36386, 14232, 45536, 302281]

theorem plane470GenLeaf0003 (x : Fin 63 → Int)
    (hroot : plane470GenOccSys.RootHolds x)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_60 : x 60 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane470GenLeaf0003Refs i).resolveCoeff plane470GenOccSys j)
    (fun i => (plane470GenLeaf0003Refs i).resolveRhs plane470GenOccSys) plane470GenLeaf0003Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane470GenLeaf0003Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 7
  · exact hroot.hOcc 9
  · exact hroot.hOcc 12
  · exact hroot.hOcc 14
  · exact hroot.hOcc 15
  · exact hroot.hOcc 19
  · exact hroot.hOcc 21
  · exact hroot.hOcc 32
  · exact hroot.hOcc 39
  · exact hroot.hOcc 42
  · exact hroot.hOcc 43
  · exact hroot.hOcc 65
  · exact hroot.hOcc 71
  · exact hroot.hOcc 72
  · exact hroot.hOcc 74
  · exact hroot.hOcc 78
  · exact hroot.hOcc 80
  · exact hroot.hOcc 82
  · exact hroot.hOcc 88
  · exact hroot.hOcc 91
  · exact hroot.hOcc 92
  · exact hroot.hOcc 96
  · exact hroot.hOcc 103
  · exact hroot.hOcc 106
  · exact hroot.hOcc 108
  · exact hroot.hOcc 112
  · exact hroot.hOcc 123
  · exact hroot.hOcc 126
  · exact hroot.hOcc 127
  · exact hroot.hOcc 129
  · exact hroot.hOcc 144
  · exact hroot.hOcc 149
  · exact hroot.hOcc 160
  · exact hroot.hOcc 162
  · exact hroot.hOcc 165
  · exact hroot.hOcc 168
  · exact hroot.hOcc 169
  · exact hroot.hOcc 179
  · exact hroot.hOcc 183
  · exact hroot.hOcc 187
  · exact hroot.hOcc 192
  · exact hroot.hOcc 197
  · exact hroot.hOcc 199
  · exact hroot.hOcc 201
  · exact hroot.hOcc 216
  · exact hroot.hOcc 222
  · change (∑ j, (-1 : Int) * x j) ≤ -plane470GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (21 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (24 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (32 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (45 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (47 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (48 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (50 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (55 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (56 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 56
  · change (∑ k, (if k = (59 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (62 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 62
  · change (∑ k, (if k = (12 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (60 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_60
  · change (∑ k, (if k = (25 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (15 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (4 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4

end QiushiMatmul
