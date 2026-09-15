import QiushiPlane456GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane456GenLeaf0006Refs : Fin 64 → RowRef 248 63 := ![.occ 0, .occ 1, .occ 4, .occ 8, .occ 12, .occ 36, .occ 39, .occ 48, .occ 52, .occ 61, .occ 65, .occ 69, .occ 72, .occ 73, .occ 80, .occ 83, .occ 88, .occ 90, .occ 93, .occ 100, .occ 109, .occ 111, .occ 139, .occ 145, .occ 146, .occ 147, .occ 153, .occ 154, .occ 159, .occ 174, .occ 176, .occ 177, .occ 179, .occ 180, .occ 186, .occ 190, .occ 192, .occ 194, .occ 198, .occ 206, .occ 207, .occ 225, .occ 227, .occ 228, .occ 238, .sumGe, .nonneg 20, .nonneg 21, .nonneg 22, .nonneg 26, .nonneg 28, .nonneg 29, .nonneg 38, .nonneg 42, .nonneg 44, .nonneg 45, .nonneg 48, .nonneg 53, .nonneg 60, .branchLe 24 (0), .branchLe 31 (0), .branchGe 57 (1), .branchLe 61 (0), .branchGe 12 (1)]

def plane456GenLeaf0006Mult : Fin 64 → Nat := ![2697, 26960, 29614, 13369, 31705, 4980, 18344, 15042, 5397, 10912, 2646, 13166, 6357, 4126, 8017, 7153, 9040, 7057, 4921, 3685, 10542, 21361, 3741, 4845, 3036, 8699, 4980, 7163, 2442, 110, 2924, 3008, 5796, 919, 12608, 1581, 837, 12447, 3309, 4659, 1877, 8668, 7882, 7336, 1989, 35446, 14905, 18243, 6732, 5131, 20369, 12363, 21433, 7911, 2591, 21939, 17616, 2048, 4750, 31705, 32522, 112734, 18382, 161955]

theorem plane456GenLeaf0006 (x : Fin 63 → Int)
    (hroot : plane456GenOccSys.RootHolds x)
    (hLB_57 : (1 : Int) ≤ x 57)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_61 : x 61 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane456GenLeaf0006Refs i).resolveCoeff plane456GenOccSys j)
    (fun i => (plane456GenLeaf0006Refs i).resolveRhs plane456GenOccSys) plane456GenLeaf0006Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane456GenLeaf0006Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 1
  · exact hroot.hOcc 4
  · exact hroot.hOcc 8
  · exact hroot.hOcc 12
  · exact hroot.hOcc 36
  · exact hroot.hOcc 39
  · exact hroot.hOcc 48
  · exact hroot.hOcc 52
  · exact hroot.hOcc 61
  · exact hroot.hOcc 65
  · exact hroot.hOcc 69
  · exact hroot.hOcc 72
  · exact hroot.hOcc 73
  · exact hroot.hOcc 80
  · exact hroot.hOcc 83
  · exact hroot.hOcc 88
  · exact hroot.hOcc 90
  · exact hroot.hOcc 93
  · exact hroot.hOcc 100
  · exact hroot.hOcc 109
  · exact hroot.hOcc 111
  · exact hroot.hOcc 139
  · exact hroot.hOcc 145
  · exact hroot.hOcc 146
  · exact hroot.hOcc 147
  · exact hroot.hOcc 153
  · exact hroot.hOcc 154
  · exact hroot.hOcc 159
  · exact hroot.hOcc 174
  · exact hroot.hOcc 176
  · exact hroot.hOcc 177
  · exact hroot.hOcc 179
  · exact hroot.hOcc 180
  · exact hroot.hOcc 186
  · exact hroot.hOcc 190
  · exact hroot.hOcc 192
  · exact hroot.hOcc 194
  · exact hroot.hOcc 198
  · exact hroot.hOcc 206
  · exact hroot.hOcc 207
  · exact hroot.hOcc 225
  · exact hroot.hOcc 227
  · exact hroot.hOcc 228
  · exact hroot.hOcc 238
  · change (∑ j, (-1 : Int) * x j) ≤ -plane456GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (20 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (21 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (22 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (26 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (28 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (29 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (38 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (42 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (44 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (45 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (48 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (53 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (60 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 60
  · change (∑ k, (if k = (24 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (31 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (57 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_57
  · change (∑ k, (if k = (61 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_61
  · change (∑ k, (if k = (12 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12

end QiushiMatmul
