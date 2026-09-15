import QiushiPlane458GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane458GenLeaf0003Refs : Fin 57 → RowRef 203 56 := ![.occ 12, .occ 30, .occ 38, .occ 46, .occ 47, .occ 48, .occ 49, .occ 51, .occ 54, .occ 61, .occ 66, .occ 75, .occ 77, .occ 84, .occ 85, .occ 93, .occ 98, .occ 99, .occ 100, .occ 106, .occ 111, .occ 114, .occ 116, .occ 119, .occ 123, .occ 128, .occ 136, .occ 149, .occ 150, .occ 152, .occ 157, .occ 159, .occ 162, .occ 167, .occ 169, .occ 173, .occ 177, .occ 178, .occ 179, .occ 186, .occ 188, .occ 201, .occ 202, .sumGe, .nonneg 0, .nonneg 13, .nonneg 23, .nonneg 36, .nonneg 39, .nonneg 52, .nonneg 53, .nonneg 55, .branchLe 46 (0), .branchGe 30 (1), .branchLe 10 (0), .branchLe 3 (0), .branchLe 40 (0)]

def plane458GenLeaf0003Mult : Fin 57 → Nat := ![97551, 833079, 33980, 7718, 39279, 431535, 98699, 63832, 524491, 337584, 1095814, 639509, 71294, 541398, 152489, 82806, 452843, 119120, 164894, 222048, 257476, 445687, 23794, 19862, 135118, 165906, 160626, 203559, 11943, 167153, 206977, 90866, 41614, 221664, 152780, 83353, 84390, 298367, 34497, 73842, 240360, 97823, 277309, 1285995, 48288, 506316, 205192, 104097, 136104, 465494, 772857, 9652, 1045635, 2271146, 1285995, 1285995, 848274]

theorem plane458GenLeaf0003 (x : Fin 56 → Int)
    (hroot : plane458GenOccSys.RootHolds x)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hUB_46 : x 46 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane458GenLeaf0003Refs i).resolveCoeff plane458GenOccSys j)
    (fun i => (plane458GenLeaf0003Refs i).resolveRhs plane458GenOccSys) plane458GenLeaf0003Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane458GenLeaf0003Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 12
  · exact hroot.hOcc 30
  · exact hroot.hOcc 38
  · exact hroot.hOcc 46
  · exact hroot.hOcc 47
  · exact hroot.hOcc 48
  · exact hroot.hOcc 49
  · exact hroot.hOcc 51
  · exact hroot.hOcc 54
  · exact hroot.hOcc 61
  · exact hroot.hOcc 66
  · exact hroot.hOcc 75
  · exact hroot.hOcc 77
  · exact hroot.hOcc 84
  · exact hroot.hOcc 85
  · exact hroot.hOcc 93
  · exact hroot.hOcc 98
  · exact hroot.hOcc 99
  · exact hroot.hOcc 100
  · exact hroot.hOcc 106
  · exact hroot.hOcc 111
  · exact hroot.hOcc 114
  · exact hroot.hOcc 116
  · exact hroot.hOcc 119
  · exact hroot.hOcc 123
  · exact hroot.hOcc 128
  · exact hroot.hOcc 136
  · exact hroot.hOcc 149
  · exact hroot.hOcc 150
  · exact hroot.hOcc 152
  · exact hroot.hOcc 157
  · exact hroot.hOcc 159
  · exact hroot.hOcc 162
  · exact hroot.hOcc 167
  · exact hroot.hOcc 169
  · exact hroot.hOcc 173
  · exact hroot.hOcc 177
  · exact hroot.hOcc 178
  · exact hroot.hOcc 179
  · exact hroot.hOcc 186
  · exact hroot.hOcc 188
  · exact hroot.hOcc 201
  · exact hroot.hOcc 202
  · change (∑ j, (-1 : Int) * x j) ≤ -plane458GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (13 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (23 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (36 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (39 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (52 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (53 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (55 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (46 : Fin 56) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_46
  · change (∑ k, (if k = (30 : Fin 56) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (10 : Fin 56) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (3 : Fin 56) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (40 : Fin 56) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40

end QiushiMatmul
