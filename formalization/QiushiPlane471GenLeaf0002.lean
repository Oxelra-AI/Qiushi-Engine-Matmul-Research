import QiushiPlane471GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane471GenLeaf0002Refs : Fin 64 → RowRef 304 63 := ![.occ 3, .occ 5, .occ 17, .occ 20, .occ 27, .occ 31, .occ 32, .occ 46, .occ 48, .occ 50, .occ 51, .occ 69, .occ 70, .occ 72, .occ 82, .occ 83, .occ 84, .occ 85, .occ 88, .occ 108, .occ 117, .occ 118, .occ 119, .occ 127, .occ 140, .occ 144, .occ 159, .occ 180, .occ 193, .occ 201, .occ 208, .occ 213, .occ 214, .occ 215, .occ 227, .occ 230, .occ 241, .occ 256, .occ 258, .occ 264, .occ 281, .occ 282, .occ 287, .occ 290, .occ 298, .occ 301, .sumGe, .nonneg 10, .nonneg 24, .nonneg 26, .nonneg 32, .nonneg 34, .nonneg 39, .nonneg 49, .nonneg 50, .nonneg 52, .nonneg 53, .nonneg 59, .nonneg 61, .branchLe 48 (0), .branchLe 14 (0), .branchLe 38 (0), .branchLe 12 (0), .branchGe 20 (1)]

def plane471GenLeaf0002Mult : Fin 64 → Nat := ![11478933, 6613834, 162971, 591786, 5306634, 4470741, 9838846, 2277604, 1023785, 233886, 311083, 913374, 272961, 10241410, 1972349, 2839555, 738587, 2949071, 230049, 3402493, 2076744, 4334031, 1982627, 5867549, 878874, 2596065, 311151, 1829846, 2196703, 1425562, 535794, 2538031, 447475, 2591412, 1156508, 2143247, 6731933, 172961, 2758562, 3844808, 394680, 564873, 3002579, 4289722, 357501, 1621326, 16102838, 2922262, 2476940, 4006441, 324092, 3278471, 5612277, 456337, 8462258, 6112135, 546846, 2430746, 5650592, 7965686, 15745337, 11586250, 8408727, 59985973]

theorem plane471GenLeaf0002 (x : Fin 63 → Int)
    (hroot : plane471GenOccSys.RootHolds x)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hUB_48 : x 48 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane471GenLeaf0002Refs i).resolveCoeff plane471GenOccSys j)
    (fun i => (plane471GenLeaf0002Refs i).resolveRhs plane471GenOccSys) plane471GenLeaf0002Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane471GenLeaf0002Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 3
  · exact hroot.hOcc 5
  · exact hroot.hOcc 17
  · exact hroot.hOcc 20
  · exact hroot.hOcc 27
  · exact hroot.hOcc 31
  · exact hroot.hOcc 32
  · exact hroot.hOcc 46
  · exact hroot.hOcc 48
  · exact hroot.hOcc 50
  · exact hroot.hOcc 51
  · exact hroot.hOcc 69
  · exact hroot.hOcc 70
  · exact hroot.hOcc 72
  · exact hroot.hOcc 82
  · exact hroot.hOcc 83
  · exact hroot.hOcc 84
  · exact hroot.hOcc 85
  · exact hroot.hOcc 88
  · exact hroot.hOcc 108
  · exact hroot.hOcc 117
  · exact hroot.hOcc 118
  · exact hroot.hOcc 119
  · exact hroot.hOcc 127
  · exact hroot.hOcc 140
  · exact hroot.hOcc 144
  · exact hroot.hOcc 159
  · exact hroot.hOcc 180
  · exact hroot.hOcc 193
  · exact hroot.hOcc 201
  · exact hroot.hOcc 208
  · exact hroot.hOcc 213
  · exact hroot.hOcc 214
  · exact hroot.hOcc 215
  · exact hroot.hOcc 227
  · exact hroot.hOcc 230
  · exact hroot.hOcc 241
  · exact hroot.hOcc 256
  · exact hroot.hOcc 258
  · exact hroot.hOcc 264
  · exact hroot.hOcc 281
  · exact hroot.hOcc 282
  · exact hroot.hOcc 287
  · exact hroot.hOcc 290
  · exact hroot.hOcc 298
  · exact hroot.hOcc 301
  · change (∑ j, (-1 : Int) * x j) ≤ -plane471GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (24 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (26 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (32 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (34 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 34
  · change (∑ k, (if k = (39 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (49 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (50 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (52 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (53 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (59 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (61 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 61
  · change (∑ k, (if k = (48 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_48
  · change (∑ k, (if k = (14 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (38 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (12 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (20 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20

end QiushiMatmul
