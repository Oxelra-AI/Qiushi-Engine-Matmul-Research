import QiushiPlane472GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane472GenLeaf0003Refs : Fin 63 → RowRef 242 62 := ![.occ 3, .occ 5, .occ 15, .occ 17, .occ 34, .occ 42, .occ 48, .occ 55, .occ 59, .occ 64, .occ 67, .occ 69, .occ 75, .occ 76, .occ 79, .occ 81, .occ 88, .occ 89, .occ 91, .occ 94, .occ 95, .occ 99, .occ 109, .occ 131, .occ 132, .occ 141, .occ 148, .occ 149, .occ 165, .occ 166, .occ 169, .occ 174, .occ 175, .occ 176, .occ 178, .occ 186, .occ 203, .occ 210, .occ 220, .occ 224, .occ 227, .occ 228, .occ 229, .occ 236, .occ 238, .sumGe, .nonneg 15, .nonneg 16, .nonneg 22, .nonneg 40, .nonneg 42, .nonneg 44, .nonneg 45, .nonneg 48, .nonneg 55, .nonneg 57, .nonneg 61, .branchLe 60 (0), .branchLe 4 (0), .branchLe 33 (0), .branchGe 11 (1), .branchLe 28 (0), .branchLe 17 (0)]

def plane472GenLeaf0003Mult : Fin 63 → Nat := ![3658068, 19309949, 34533976, 1583753, 9328369, 3569125, 13930869, 3778150, 33153766, 17318445, 20415181, 16433764, 15028360, 31246978, 11553625, 3705224, 32387578, 17275734, 10067544, 12751420, 6277807, 17943583, 3241509, 15103373, 11283224, 13873017, 7475069, 5704339, 4506463, 817524, 15859686, 10002636, 8833694, 9118700, 14971799, 5643771, 15841090, 5935600, 7348728, 15674626, 15172040, 4762519, 11000084, 18756182, 8982266, 97687648, 15058045, 5894183, 16655618, 33676495, 3315786, 3301482, 10171054, 22935359, 64680811, 105940, 24962168, 62127658, 88705382, 72774305, 99310971, 48172731, 80173709]

theorem plane472GenLeaf0003 (x : Fin 62 → Int)
    (hroot : plane472GenOccSys.RootHolds x)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hUB_60 : x 60 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane472GenLeaf0003Refs i).resolveCoeff plane472GenOccSys j)
    (fun i => (plane472GenLeaf0003Refs i).resolveRhs plane472GenOccSys) plane472GenLeaf0003Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane472GenLeaf0003Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 3
  · exact hroot.hOcc 5
  · exact hroot.hOcc 15
  · exact hroot.hOcc 17
  · exact hroot.hOcc 34
  · exact hroot.hOcc 42
  · exact hroot.hOcc 48
  · exact hroot.hOcc 55
  · exact hroot.hOcc 59
  · exact hroot.hOcc 64
  · exact hroot.hOcc 67
  · exact hroot.hOcc 69
  · exact hroot.hOcc 75
  · exact hroot.hOcc 76
  · exact hroot.hOcc 79
  · exact hroot.hOcc 81
  · exact hroot.hOcc 88
  · exact hroot.hOcc 89
  · exact hroot.hOcc 91
  · exact hroot.hOcc 94
  · exact hroot.hOcc 95
  · exact hroot.hOcc 99
  · exact hroot.hOcc 109
  · exact hroot.hOcc 131
  · exact hroot.hOcc 132
  · exact hroot.hOcc 141
  · exact hroot.hOcc 148
  · exact hroot.hOcc 149
  · exact hroot.hOcc 165
  · exact hroot.hOcc 166
  · exact hroot.hOcc 169
  · exact hroot.hOcc 174
  · exact hroot.hOcc 175
  · exact hroot.hOcc 176
  · exact hroot.hOcc 178
  · exact hroot.hOcc 186
  · exact hroot.hOcc 203
  · exact hroot.hOcc 210
  · exact hroot.hOcc 220
  · exact hroot.hOcc 224
  · exact hroot.hOcc 227
  · exact hroot.hOcc 228
  · exact hroot.hOcc 229
  · exact hroot.hOcc 236
  · exact hroot.hOcc 238
  · change (∑ j, (-1 : Int) * x j) ≤ -plane472GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (16 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (22 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (40 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (42 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (44 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (45 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (48 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (55 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (57 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 57
  · change (∑ k, (if k = (61 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 61
  · change (∑ k, (if k = (60 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_60
  · change (∑ k, (if k = (4 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (33 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (11 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11
  · change (∑ k, (if k = (28 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (17 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17

end QiushiMatmul
