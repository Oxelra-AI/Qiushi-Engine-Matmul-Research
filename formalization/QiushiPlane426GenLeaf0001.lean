import QiushiPlane426GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane426GenLeaf0001Refs : Fin 59 → RowRef 340 58 := ![.occ 8, .occ 24, .occ 74, .occ 76, .occ 77, .occ 84, .occ 86, .occ 87, .occ 88, .occ 99, .occ 100, .occ 104, .occ 113, .occ 116, .occ 117, .occ 122, .occ 126, .occ 155, .occ 163, .occ 172, .occ 178, .occ 179, .occ 186, .occ 194, .occ 205, .occ 206, .occ 208, .occ 223, .occ 249, .occ 252, .occ 253, .occ 256, .occ 260, .occ 268, .occ 290, .occ 300, .occ 321, .occ 322, .occ 323, .occ 325, .occ 327, .occ 328, .occ 333, .occ 334, .sumGe, .nonneg 6, .nonneg 16, .nonneg 17, .nonneg 30, .nonneg 36, .nonneg 40, .nonneg 42, .branchLe 43 (0), .branchLe 14 (0), .branchLe 1 (0), .branchLe 13 (0), .branchLe 37 (0), .branchGe 21 (1), .branchLe 35 (0)]

def plane426GenLeaf0001Mult : Fin 59 → Nat := ![632094, 54756, 669524, 1811756, 245012, 1924712, 1186076, 557080, 2759724, 1965200, 355140, 1581012, 2222848, 2013720, 1817272, 2729608, 1269406, 2855640, 4206796, 626796, 1809500, 1345468, 76618, 228388, 1976706, 89246, 2109714, 164438, 1807650, 112932, 1383422, 32308, 1654384, 24390, 1831644, 322684, 96918, 214643, 273277, 896194, 204690, 1721624, 275469, 781005, 8564074, 387012, 7826414, 11883952, 6500, 2506496, 4864636, 369140, 4056444, 3627760, 4069528, 5072204, 2064728, 14093786, 5133460]

theorem plane426GenLeaf0001 (x : Fin 58 → Int)
    (hroot : plane426GenOccSys.RootHolds x)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hUB_43 : x 43 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane426GenLeaf0001Refs i).resolveCoeff plane426GenOccSys j)
    (fun i => (plane426GenLeaf0001Refs i).resolveRhs plane426GenOccSys) plane426GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane426GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 8
  · exact hroot.hOcc 24
  · exact hroot.hOcc 74
  · exact hroot.hOcc 76
  · exact hroot.hOcc 77
  · exact hroot.hOcc 84
  · exact hroot.hOcc 86
  · exact hroot.hOcc 87
  · exact hroot.hOcc 88
  · exact hroot.hOcc 99
  · exact hroot.hOcc 100
  · exact hroot.hOcc 104
  · exact hroot.hOcc 113
  · exact hroot.hOcc 116
  · exact hroot.hOcc 117
  · exact hroot.hOcc 122
  · exact hroot.hOcc 126
  · exact hroot.hOcc 155
  · exact hroot.hOcc 163
  · exact hroot.hOcc 172
  · exact hroot.hOcc 178
  · exact hroot.hOcc 179
  · exact hroot.hOcc 186
  · exact hroot.hOcc 194
  · exact hroot.hOcc 205
  · exact hroot.hOcc 206
  · exact hroot.hOcc 208
  · exact hroot.hOcc 223
  · exact hroot.hOcc 249
  · exact hroot.hOcc 252
  · exact hroot.hOcc 253
  · exact hroot.hOcc 256
  · exact hroot.hOcc 260
  · exact hroot.hOcc 268
  · exact hroot.hOcc 290
  · exact hroot.hOcc 300
  · exact hroot.hOcc 321
  · exact hroot.hOcc 322
  · exact hroot.hOcc 323
  · exact hroot.hOcc 325
  · exact hroot.hOcc 327
  · exact hroot.hOcc 328
  · exact hroot.hOcc 333
  · exact hroot.hOcc 334
  · change (∑ j, (-1 : Int) * x j) ≤ -plane426GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (16 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (30 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (36 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (40 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (42 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (43 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (14 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (13 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (37 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (21 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21
  · change (∑ k, (if k = (35 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35

end QiushiMatmul
