import QiushiPlane469GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane469GenLeaf0006Refs : Fin 61 → RowRef 217 60 := ![.occ 3, .occ 4, .occ 6, .occ 8, .occ 10, .occ 15, .occ 18, .occ 21, .occ 25, .occ 42, .occ 45, .occ 47, .occ 55, .occ 57, .occ 58, .occ 59, .occ 61, .occ 68, .occ 73, .occ 83, .occ 84, .occ 93, .occ 97, .occ 109, .occ 110, .occ 114, .occ 118, .occ 119, .occ 130, .occ 134, .occ 139, .occ 144, .occ 146, .occ 147, .occ 149, .occ 150, .occ 156, .occ 167, .occ 168, .occ 169, .occ 178, .occ 186, .occ 202, .occ 206, .sumGe, .nonneg 7, .nonneg 10, .nonneg 13, .nonneg 17, .nonneg 19, .nonneg 32, .nonneg 35, .nonneg 41, .nonneg 45, .nonneg 46, .nonneg 50, .nonneg 52, .nonneg 55, .nonneg 58, .branchLe 34 (0), .branchGe 8 (1)]

def plane469GenLeaf0006Mult : Fin 61 → Nat := ![163921, 80185, 9834, 22907, 57918, 32438, 25867, 2222, 5611, 29378, 105595, 146965, 61229, 16103, 51368, 50371, 2477, 103012, 812, 22648, 36204, 256528, 165809, 23034, 732, 54629, 63533, 103508, 122351, 166527, 6545, 1936, 104725, 64580, 4058, 109874, 46129, 12670, 7924, 45637, 24303, 27654, 17758, 4890, 279176, 36677, 46498, 62936, 35270, 9256, 23077, 54884, 10522, 76429, 701479, 18395, 72838, 662040, 124928, 151803, 1458909]

theorem plane469GenLeaf0006 (x : Fin 60 → Int)
    (hroot : plane469GenOccSys.RootHolds x)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hUB_34 : x 34 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane469GenLeaf0006Refs i).resolveCoeff plane469GenOccSys j)
    (fun i => (plane469GenLeaf0006Refs i).resolveRhs plane469GenOccSys) plane469GenLeaf0006Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane469GenLeaf0006Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 3
  · exact hroot.hOcc 4
  · exact hroot.hOcc 6
  · exact hroot.hOcc 8
  · exact hroot.hOcc 10
  · exact hroot.hOcc 15
  · exact hroot.hOcc 18
  · exact hroot.hOcc 21
  · exact hroot.hOcc 25
  · exact hroot.hOcc 42
  · exact hroot.hOcc 45
  · exact hroot.hOcc 47
  · exact hroot.hOcc 55
  · exact hroot.hOcc 57
  · exact hroot.hOcc 58
  · exact hroot.hOcc 59
  · exact hroot.hOcc 61
  · exact hroot.hOcc 68
  · exact hroot.hOcc 73
  · exact hroot.hOcc 83
  · exact hroot.hOcc 84
  · exact hroot.hOcc 93
  · exact hroot.hOcc 97
  · exact hroot.hOcc 109
  · exact hroot.hOcc 110
  · exact hroot.hOcc 114
  · exact hroot.hOcc 118
  · exact hroot.hOcc 119
  · exact hroot.hOcc 130
  · exact hroot.hOcc 134
  · exact hroot.hOcc 139
  · exact hroot.hOcc 144
  · exact hroot.hOcc 146
  · exact hroot.hOcc 147
  · exact hroot.hOcc 149
  · exact hroot.hOcc 150
  · exact hroot.hOcc 156
  · exact hroot.hOcc 167
  · exact hroot.hOcc 168
  · exact hroot.hOcc 169
  · exact hroot.hOcc 178
  · exact hroot.hOcc 186
  · exact hroot.hOcc 202
  · exact hroot.hOcc 206
  · change (∑ j, (-1 : Int) * x j) ≤ -plane469GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (10 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (13 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (17 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (19 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (32 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (35 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 35
  · change (∑ k, (if k = (41 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (45 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (46 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (50 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (52 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (55 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (58 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 58
  · change (∑ k, (if k = (34 : Fin 60) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (8 : Fin 60) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8

end QiushiMatmul
