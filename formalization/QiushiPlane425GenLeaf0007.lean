import QiushiPlane425GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane425GenLeaf0007Refs : Fin 58 → RowRef 202 58 := ![.occ 30, .occ 35, .occ 38, .occ 49, .occ 60, .occ 61, .occ 62, .occ 65, .occ 66, .occ 69, .occ 72, .occ 76, .occ 83, .occ 88, .occ 108, .occ 111, .occ 117, .occ 127, .occ 133, .occ 138, .occ 142, .occ 143, .occ 145, .occ 149, .occ 153, .occ 161, .occ 163, .occ 164, .occ 167, .occ 170, .occ 171, .occ 172, .occ 174, .occ 179, .occ 180, .occ 186, .occ 190, .occ 191, .occ 192, .occ 195, .occ 196, .occ 199, .sumGe, .nonneg 2, .nonneg 3, .nonneg 13, .nonneg 14, .nonneg 24, .nonneg 32, .nonneg 34, .nonneg 38, .nonneg 41, .nonneg 48, .nonneg 55, .branchGe 17 (1), .branchLe 9 (0), .branchGe 43 (1), .branchGe 12 (1)]

def plane425GenLeaf0007Mult : Fin 58 → Nat := ![202882, 304388, 73774, 180920, 233708, 24678, 1456306, 258672, 399502, 2530120, 308882, 354932, 31632, 470262, 250544, 294264, 35866, 286625, 165596, 137611, 1143294, 163196, 70046, 198486, 251558, 1013980, 125418, 53868, 100000, 694698, 14753, 154495, 214258, 939164, 780111, 576286, 567198, 173047, 174138, 395049, 1217149, 97846, 3098216, 2355798, 388614, 740628, 73482, 289050, 3097374, 147594, 808668, 1008028, 1091466, 230614, 9523028, 1924490, 4256928, 2355798]

theorem plane425GenLeaf0007 (x : Fin 58 → Int)
    (hroot : plane425GenOccSys.RootHolds x)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hLB_43 : (1 : Int) ≤ x 43)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hUB_9 : x 9 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane425GenLeaf0007Refs i).resolveCoeff plane425GenOccSys j)
    (fun i => (plane425GenLeaf0007Refs i).resolveRhs plane425GenOccSys) plane425GenLeaf0007Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane425GenLeaf0007Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 30
  · exact hroot.hOcc 35
  · exact hroot.hOcc 38
  · exact hroot.hOcc 49
  · exact hroot.hOcc 60
  · exact hroot.hOcc 61
  · exact hroot.hOcc 62
  · exact hroot.hOcc 65
  · exact hroot.hOcc 66
  · exact hroot.hOcc 69
  · exact hroot.hOcc 72
  · exact hroot.hOcc 76
  · exact hroot.hOcc 83
  · exact hroot.hOcc 88
  · exact hroot.hOcc 108
  · exact hroot.hOcc 111
  · exact hroot.hOcc 117
  · exact hroot.hOcc 127
  · exact hroot.hOcc 133
  · exact hroot.hOcc 138
  · exact hroot.hOcc 142
  · exact hroot.hOcc 143
  · exact hroot.hOcc 145
  · exact hroot.hOcc 149
  · exact hroot.hOcc 153
  · exact hroot.hOcc 161
  · exact hroot.hOcc 163
  · exact hroot.hOcc 164
  · exact hroot.hOcc 167
  · exact hroot.hOcc 170
  · exact hroot.hOcc 171
  · exact hroot.hOcc 172
  · exact hroot.hOcc 174
  · exact hroot.hOcc 179
  · exact hroot.hOcc 180
  · exact hroot.hOcc 186
  · exact hroot.hOcc 190
  · exact hroot.hOcc 191
  · exact hroot.hOcc 192
  · exact hroot.hOcc 195
  · exact hroot.hOcc 196
  · exact hroot.hOcc 199
  · change (∑ j, (-1 : Int) * x j) ≤ -plane425GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (3 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (13 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (14 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (24 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (32 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (34 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 34
  · change (∑ k, (if k = (38 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (41 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (48 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (55 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (17 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17
  · change (∑ k, (if k = (9 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (43 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_43
  · change (∑ k, (if k = (12 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12

end QiushiMatmul
