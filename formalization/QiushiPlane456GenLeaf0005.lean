import QiushiPlane456GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane456GenLeaf0005Refs : Fin 64 → RowRef 248 63 := ![.occ 31, .occ 36, .occ 37, .occ 38, .occ 39, .occ 44, .occ 45, .occ 47, .occ 50, .occ 53, .occ 55, .occ 61, .occ 72, .occ 79, .occ 82, .occ 88, .occ 90, .occ 93, .occ 98, .occ 100, .occ 110, .occ 112, .occ 113, .occ 115, .occ 124, .occ 134, .occ 135, .occ 139, .occ 151, .occ 160, .occ 173, .occ 174, .occ 175, .occ 176, .occ 177, .occ 179, .occ 183, .occ 207, .occ 227, .occ 228, .occ 230, .occ 231, .occ 233, .occ 234, .occ 238, .occ 240, .occ 241, .sumGe, .nonneg 7, .nonneg 19, .nonneg 26, .nonneg 28, .nonneg 33, .nonneg 37, .nonneg 38, .nonneg 42, .nonneg 44, .nonneg 49, .nonneg 60, .branchLe 24 (0), .branchLe 31 (0), .branchGe 57 (1), .branchLe 61 (0), .branchLe 12 (0)]

def plane456GenLeaf0005Mult : Fin 64 → Nat := ![321513, 742242, 194853, 2621990, 628619, 152895, 91906, 726188, 1141287, 185097, 608150, 1819623, 1571993, 749659, 89643, 558758, 682043, 530179, 551207, 326912, 747547, 162582, 52654, 39342, 615949, 394291, 503211, 1048218, 1112783, 334133, 217085, 297428, 180290, 901051, 138089, 1126417, 447367, 60605, 164664, 227126, 272347, 228931, 25079, 210597, 639718, 88157, 561104, 3399363, 875008, 368423, 448857, 1290986, 41311, 1016121, 1962374, 572801, 1169833, 186590, 668400, 1843618, 1392478, 9378064, 3174094, 2399141]

theorem plane456GenLeaf0005 (x : Fin 63 → Int)
    (hroot : plane456GenOccSys.RootHolds x)
    (hLB_57 : (1 : Int) ≤ x 57)
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_61 : x 61 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane456GenLeaf0005Refs i).resolveCoeff plane456GenOccSys j)
    (fun i => (plane456GenLeaf0005Refs i).resolveRhs plane456GenOccSys) plane456GenLeaf0005Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane456GenLeaf0005Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 31
  · exact hroot.hOcc 36
  · exact hroot.hOcc 37
  · exact hroot.hOcc 38
  · exact hroot.hOcc 39
  · exact hroot.hOcc 44
  · exact hroot.hOcc 45
  · exact hroot.hOcc 47
  · exact hroot.hOcc 50
  · exact hroot.hOcc 53
  · exact hroot.hOcc 55
  · exact hroot.hOcc 61
  · exact hroot.hOcc 72
  · exact hroot.hOcc 79
  · exact hroot.hOcc 82
  · exact hroot.hOcc 88
  · exact hroot.hOcc 90
  · exact hroot.hOcc 93
  · exact hroot.hOcc 98
  · exact hroot.hOcc 100
  · exact hroot.hOcc 110
  · exact hroot.hOcc 112
  · exact hroot.hOcc 113
  · exact hroot.hOcc 115
  · exact hroot.hOcc 124
  · exact hroot.hOcc 134
  · exact hroot.hOcc 135
  · exact hroot.hOcc 139
  · exact hroot.hOcc 151
  · exact hroot.hOcc 160
  · exact hroot.hOcc 173
  · exact hroot.hOcc 174
  · exact hroot.hOcc 175
  · exact hroot.hOcc 176
  · exact hroot.hOcc 177
  · exact hroot.hOcc 179
  · exact hroot.hOcc 183
  · exact hroot.hOcc 207
  · exact hroot.hOcc 227
  · exact hroot.hOcc 228
  · exact hroot.hOcc 230
  · exact hroot.hOcc 231
  · exact hroot.hOcc 233
  · exact hroot.hOcc 234
  · exact hroot.hOcc 238
  · exact hroot.hOcc 240
  · exact hroot.hOcc 241
  · change (∑ j, (-1 : Int) * x j) ≤ -plane456GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (19 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (26 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (28 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (33 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (37 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (38 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (42 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (44 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (49 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (60 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 60
  · change (∑ k, (if k = (24 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (31 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (57 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_57
  · change (∑ k, (if k = (61 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_61
  · change (∑ k, (if k = (12 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12

end QiushiMatmul
