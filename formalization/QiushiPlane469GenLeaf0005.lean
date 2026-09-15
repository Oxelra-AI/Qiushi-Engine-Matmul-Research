import QiushiPlane469GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane469GenLeaf0005Refs : Fin 61 → RowRef 217 60 := ![.occ 16, .occ 17, .occ 18, .occ 21, .occ 32, .occ 33, .occ 35, .occ 36, .occ 37, .occ 38, .occ 39, .occ 43, .occ 49, .occ 57, .occ 58, .occ 68, .occ 69, .occ 75, .occ 82, .occ 83, .occ 84, .occ 85, .occ 86, .occ 90, .occ 92, .occ 94, .occ 105, .occ 108, .occ 110, .occ 132, .occ 139, .occ 144, .occ 147, .occ 148, .occ 154, .occ 155, .occ 156, .occ 174, .occ 175, .occ 179, .occ 181, .occ 183, .occ 189, .occ 191, .occ 195, .occ 200, .occ 209, .sumGe, .nonneg 3, .nonneg 7, .nonneg 10, .nonneg 14, .nonneg 17, .nonneg 25, .nonneg 32, .nonneg 39, .nonneg 46, .branchLe 34 (0), .branchLe 13 (0), .branchLe 8 (0), .branchGe 54 (1)]

def plane469GenLeaf0005Mult : Fin 61 → Nat := ![327008, 106551, 302877, 373976, 557319, 86157, 1154174, 1287920, 1559849, 1223457, 694936, 341009, 615089, 518523, 84789, 67394, 329633, 62034, 115416, 1150689, 1186845, 1030277, 131772, 282412, 925187, 535321, 513609, 88010, 497497, 209026, 257588, 7803, 217258, 297044, 136037, 150984, 396058, 84523, 161600, 85983, 81722, 193596, 30627, 302556, 277494, 185266, 84789, 1675265, 478359, 1827884, 85101, 30103, 834016, 660860, 531467, 202417, 1540678, 84789, 931295, 610225, 12235456]

theorem plane469GenLeaf0005 (x : Fin 60 → Int)
    (hroot : plane469GenOccSys.RootHolds x)
    (hLB_54 : (1 : Int) ≤ x 54)
    (hUB_34 : x 34 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane469GenLeaf0005Refs i).resolveCoeff plane469GenOccSys j)
    (fun i => (plane469GenLeaf0005Refs i).resolveRhs plane469GenOccSys) plane469GenLeaf0005Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane469GenLeaf0005Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 16
  · exact hroot.hOcc 17
  · exact hroot.hOcc 18
  · exact hroot.hOcc 21
  · exact hroot.hOcc 32
  · exact hroot.hOcc 33
  · exact hroot.hOcc 35
  · exact hroot.hOcc 36
  · exact hroot.hOcc 37
  · exact hroot.hOcc 38
  · exact hroot.hOcc 39
  · exact hroot.hOcc 43
  · exact hroot.hOcc 49
  · exact hroot.hOcc 57
  · exact hroot.hOcc 58
  · exact hroot.hOcc 68
  · exact hroot.hOcc 69
  · exact hroot.hOcc 75
  · exact hroot.hOcc 82
  · exact hroot.hOcc 83
  · exact hroot.hOcc 84
  · exact hroot.hOcc 85
  · exact hroot.hOcc 86
  · exact hroot.hOcc 90
  · exact hroot.hOcc 92
  · exact hroot.hOcc 94
  · exact hroot.hOcc 105
  · exact hroot.hOcc 108
  · exact hroot.hOcc 110
  · exact hroot.hOcc 132
  · exact hroot.hOcc 139
  · exact hroot.hOcc 144
  · exact hroot.hOcc 147
  · exact hroot.hOcc 148
  · exact hroot.hOcc 154
  · exact hroot.hOcc 155
  · exact hroot.hOcc 156
  · exact hroot.hOcc 174
  · exact hroot.hOcc 175
  · exact hroot.hOcc 179
  · exact hroot.hOcc 181
  · exact hroot.hOcc 183
  · exact hroot.hOcc 189
  · exact hroot.hOcc 191
  · exact hroot.hOcc 195
  · exact hroot.hOcc 200
  · exact hroot.hOcc 209
  · change (∑ j, (-1 : Int) * x j) ≤ -plane469GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (7 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (10 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (14 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (17 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (25 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (32 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (39 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (46 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (34 : Fin 60) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (13 : Fin 60) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (8 : Fin 60) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (54 : Fin 60) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_54

end QiushiMatmul
