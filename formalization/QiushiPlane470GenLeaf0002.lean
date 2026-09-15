import QiushiPlane470GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane470GenLeaf0002Refs : Fin 64 → RowRef 232 63 := ![.occ 2, .occ 25, .occ 29, .occ 39, .occ 45, .occ 46, .occ 49, .occ 51, .occ 67, .occ 68, .occ 72, .occ 74, .occ 80, .occ 88, .occ 92, .occ 96, .occ 98, .occ 100, .occ 103, .occ 106, .occ 108, .occ 110, .occ 112, .occ 116, .occ 126, .occ 129, .occ 142, .occ 149, .occ 154, .occ 155, .occ 171, .occ 172, .occ 174, .occ 175, .occ 176, .occ 181, .occ 183, .occ 192, .occ 196, .occ 207, .occ 210, .occ 212, .occ 216, .occ 218, .occ 221, .occ 226, .sumGe, .nonneg 10, .nonneg 21, .nonneg 32, .nonneg 40, .nonneg 45, .nonneg 49, .nonneg 50, .nonneg 51, .nonneg 55, .nonneg 59, .nonneg 62, .branchLe 12 (0), .branchLe 60 (0), .branchLe 25 (0), .branchLe 15 (0), .branchLe 4 (0), .branchGe 23 (1)]

def plane470GenLeaf0002Mult : Fin 64 → Nat := ![545537, 633948, 114038, 524034, 205615, 85603, 33099, 737284, 1383, 548372, 445482, 108648, 402436, 244042, 4551, 375127, 489031, 157477, 105390, 316867, 22319, 107746, 502361, 20744, 104312, 152534, 81867, 42477, 372021, 87534, 324495, 308363, 231210, 236265, 191563, 164536, 231300, 366885, 86726, 207230, 65099, 354889, 353993, 22506, 80089, 205405, 1607542, 428867, 493793, 534983, 231638, 155737, 146541, 195441, 700633, 1295016, 219472, 569943, 1299542, 932336, 1585036, 436764, 1412168, 4148215]

theorem plane470GenLeaf0002 (x : Fin 63 → Int)
    (hroot : plane470GenOccSys.RootHolds x)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_60 : x 60 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane470GenLeaf0002Refs i).resolveCoeff plane470GenOccSys j)
    (fun i => (plane470GenLeaf0002Refs i).resolveRhs plane470GenOccSys) plane470GenLeaf0002Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane470GenLeaf0002Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · exact hroot.hOcc 25
  · exact hroot.hOcc 29
  · exact hroot.hOcc 39
  · exact hroot.hOcc 45
  · exact hroot.hOcc 46
  · exact hroot.hOcc 49
  · exact hroot.hOcc 51
  · exact hroot.hOcc 67
  · exact hroot.hOcc 68
  · exact hroot.hOcc 72
  · exact hroot.hOcc 74
  · exact hroot.hOcc 80
  · exact hroot.hOcc 88
  · exact hroot.hOcc 92
  · exact hroot.hOcc 96
  · exact hroot.hOcc 98
  · exact hroot.hOcc 100
  · exact hroot.hOcc 103
  · exact hroot.hOcc 106
  · exact hroot.hOcc 108
  · exact hroot.hOcc 110
  · exact hroot.hOcc 112
  · exact hroot.hOcc 116
  · exact hroot.hOcc 126
  · exact hroot.hOcc 129
  · exact hroot.hOcc 142
  · exact hroot.hOcc 149
  · exact hroot.hOcc 154
  · exact hroot.hOcc 155
  · exact hroot.hOcc 171
  · exact hroot.hOcc 172
  · exact hroot.hOcc 174
  · exact hroot.hOcc 175
  · exact hroot.hOcc 176
  · exact hroot.hOcc 181
  · exact hroot.hOcc 183
  · exact hroot.hOcc 192
  · exact hroot.hOcc 196
  · exact hroot.hOcc 207
  · exact hroot.hOcc 210
  · exact hroot.hOcc 212
  · exact hroot.hOcc 216
  · exact hroot.hOcc 218
  · exact hroot.hOcc 221
  · exact hroot.hOcc 226
  · change (∑ j, (-1 : Int) * x j) ≤ -plane470GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (21 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (32 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (40 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (45 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (49 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (50 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (51 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 51
  · change (∑ k, (if k = (55 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (59 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (62 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 62
  · change (∑ k, (if k = (12 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (60 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_60
  · change (∑ k, (if k = (25 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (15 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (4 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23

end QiushiMatmul
