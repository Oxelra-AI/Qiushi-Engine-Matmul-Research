import QiushiPlane425GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane425GenLeaf0006Refs : Fin 59 → RowRef 202 58 := ![.occ 27, .occ 30, .occ 33, .occ 34, .occ 35, .occ 62, .occ 63, .occ 65, .occ 66, .occ 69, .occ 71, .occ 82, .occ 89, .occ 93, .occ 110, .occ 113, .occ 114, .occ 117, .occ 122, .occ 125, .occ 127, .occ 129, .occ 131, .occ 132, .occ 133, .occ 135, .occ 138, .occ 143, .occ 151, .occ 153, .occ 155, .occ 164, .occ 170, .occ 174, .occ 175, .occ 182, .occ 186, .occ 188, .occ 190, .occ 192, .occ 198, .occ 199, .occ 200, .occ 201, .sumGe, .nonneg 2, .nonneg 3, .nonneg 13, .nonneg 14, .nonneg 15, .nonneg 22, .nonneg 32, .nonneg 38, .nonneg 41, .nonneg 48, .branchGe 17 (1), .branchLe 9 (0), .branchGe 43 (1), .branchLe 12 (0)]

def plane425GenLeaf0006Mult : Fin 59 → Nat := ![2764, 3372, 1752, 7832, 1840, 6812, 2580, 7040, 3224, 23344, 5916, 1568, 3464, 2212, 2948, 550, 3552, 3562, 3162, 3612, 902, 496, 456, 18, 1102, 2028, 6620, 1380, 1084, 4254, 2718, 4238, 4006, 6330, 1594, 2884, 3006, 2184, 2532, 8207, 388, 8591, 3129, 1415, 29648, 12260, 19572, 8220, 18520, 15748, 4736, 26904, 3684, 7132, 13048, 39116, 14928, 52608, 29648]

theorem plane425GenLeaf0006 (x : Fin 58 → Int)
    (hroot : plane425GenOccSys.RootHolds x)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hLB_43 : (1 : Int) ≤ x 43)
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane425GenLeaf0006Refs i).resolveCoeff plane425GenOccSys j)
    (fun i => (plane425GenLeaf0006Refs i).resolveRhs plane425GenOccSys) plane425GenLeaf0006Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane425GenLeaf0006Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 27
  · exact hroot.hOcc 30
  · exact hroot.hOcc 33
  · exact hroot.hOcc 34
  · exact hroot.hOcc 35
  · exact hroot.hOcc 62
  · exact hroot.hOcc 63
  · exact hroot.hOcc 65
  · exact hroot.hOcc 66
  · exact hroot.hOcc 69
  · exact hroot.hOcc 71
  · exact hroot.hOcc 82
  · exact hroot.hOcc 89
  · exact hroot.hOcc 93
  · exact hroot.hOcc 110
  · exact hroot.hOcc 113
  · exact hroot.hOcc 114
  · exact hroot.hOcc 117
  · exact hroot.hOcc 122
  · exact hroot.hOcc 125
  · exact hroot.hOcc 127
  · exact hroot.hOcc 129
  · exact hroot.hOcc 131
  · exact hroot.hOcc 132
  · exact hroot.hOcc 133
  · exact hroot.hOcc 135
  · exact hroot.hOcc 138
  · exact hroot.hOcc 143
  · exact hroot.hOcc 151
  · exact hroot.hOcc 153
  · exact hroot.hOcc 155
  · exact hroot.hOcc 164
  · exact hroot.hOcc 170
  · exact hroot.hOcc 174
  · exact hroot.hOcc 175
  · exact hroot.hOcc 182
  · exact hroot.hOcc 186
  · exact hroot.hOcc 188
  · exact hroot.hOcc 190
  · exact hroot.hOcc 192
  · exact hroot.hOcc 198
  · exact hroot.hOcc 199
  · exact hroot.hOcc 200
  · exact hroot.hOcc 201
  · change (∑ j, (-1 : Int) * x j) ≤ -plane425GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (3 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (13 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (14 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (15 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (22 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (32 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (38 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (41 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (48 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (17 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17
  · change (∑ k, (if k = (9 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (43 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_43
  · change (∑ k, (if k = (12 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12

end QiushiMatmul
