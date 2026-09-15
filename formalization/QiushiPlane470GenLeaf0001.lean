import QiushiPlane470GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane470GenLeaf0001Refs : Fin 64 → RowRef 232 63 := ![.occ 13, .occ 20, .occ 22, .occ 23, .occ 27, .occ 31, .occ 35, .occ 40, .occ 67, .occ 72, .occ 74, .occ 79, .occ 80, .occ 85, .occ 88, .occ 92, .occ 93, .occ 94, .occ 97, .occ 103, .occ 106, .occ 108, .occ 110, .occ 111, .occ 115, .occ 118, .occ 121, .occ 124, .occ 126, .occ 129, .occ 146, .occ 147, .occ 155, .occ 156, .occ 161, .occ 165, .occ 171, .occ 172, .occ 180, .occ 181, .occ 183, .occ 196, .occ 198, .occ 204, .occ 212, .occ 216, .occ 217, .occ 222, .occ 227, .sumGe, .nonneg 10, .nonneg 16, .nonneg 20, .nonneg 32, .nonneg 47, .nonneg 55, .nonneg 62, .branchLe 12 (0), .branchLe 60 (0), .branchLe 25 (0), .branchLe 15 (0), .branchLe 4 (0), .branchGe 9 (1), .branchLe 23 (0)]

def plane470GenLeaf0001Mult : Fin 64 → Nat := ![1392721254, 44754710, 2147850554, 1939206604, 1670961484, 1542557542, 2310557238, 1562964448, 2322512481, 648434006, 1086567050, 198938052, 5813274399, 459295892, 5091386624, 2873890007, 1100830147, 1162670723, 52479593, 2650884946, 1522229198, 843765468, 1255555773, 2777599821, 1944264426, 903139200, 1738391016, 728059439, 1907674626, 791550537, 785887212, 1475332895, 105147752, 120107264, 783316121, 481648002, 876759516, 1429289519, 783504742, 2779224803, 3268742948, 560195974, 1145475134, 2685068938, 682410909, 2792556117, 160833732, 2418167642, 1941098666, 13244037176, 5182001746, 744722282, 1466467344, 2451291096, 4387009468, 6839193898, 656955734, 9557019214, 8065406448, 7356958380, 11648882226, 11597274152, 2767574488, 12367277660]

theorem plane470GenLeaf0001 (x : Fin 63 → Int)
    (hroot : plane470GenOccSys.RootHolds x)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_60 : x 60 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane470GenLeaf0001Refs i).resolveCoeff plane470GenOccSys j)
    (fun i => (plane470GenLeaf0001Refs i).resolveRhs plane470GenOccSys) plane470GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane470GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 13
  · exact hroot.hOcc 20
  · exact hroot.hOcc 22
  · exact hroot.hOcc 23
  · exact hroot.hOcc 27
  · exact hroot.hOcc 31
  · exact hroot.hOcc 35
  · exact hroot.hOcc 40
  · exact hroot.hOcc 67
  · exact hroot.hOcc 72
  · exact hroot.hOcc 74
  · exact hroot.hOcc 79
  · exact hroot.hOcc 80
  · exact hroot.hOcc 85
  · exact hroot.hOcc 88
  · exact hroot.hOcc 92
  · exact hroot.hOcc 93
  · exact hroot.hOcc 94
  · exact hroot.hOcc 97
  · exact hroot.hOcc 103
  · exact hroot.hOcc 106
  · exact hroot.hOcc 108
  · exact hroot.hOcc 110
  · exact hroot.hOcc 111
  · exact hroot.hOcc 115
  · exact hroot.hOcc 118
  · exact hroot.hOcc 121
  · exact hroot.hOcc 124
  · exact hroot.hOcc 126
  · exact hroot.hOcc 129
  · exact hroot.hOcc 146
  · exact hroot.hOcc 147
  · exact hroot.hOcc 155
  · exact hroot.hOcc 156
  · exact hroot.hOcc 161
  · exact hroot.hOcc 165
  · exact hroot.hOcc 171
  · exact hroot.hOcc 172
  · exact hroot.hOcc 180
  · exact hroot.hOcc 181
  · exact hroot.hOcc 183
  · exact hroot.hOcc 196
  · exact hroot.hOcc 198
  · exact hroot.hOcc 204
  · exact hroot.hOcc 212
  · exact hroot.hOcc 216
  · exact hroot.hOcc 217
  · exact hroot.hOcc 222
  · exact hroot.hOcc 227
  · change (∑ j, (-1 : Int) * x j) ≤ -plane470GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (16 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (20 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (32 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (47 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (55 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (62 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 62
  · change (∑ k, (if k = (12 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (60 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_60
  · change (∑ k, (if k = (25 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (15 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (4 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (9 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9
  · change (∑ k, (if k = (23 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23

end QiushiMatmul
