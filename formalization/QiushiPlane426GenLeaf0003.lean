import QiushiPlane426GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane426GenLeaf0003Refs : Fin 59 → RowRef 340 58 := ![.occ 25, .occ 48, .occ 49, .occ 53, .occ 66, .occ 76, .occ 77, .occ 84, .occ 86, .occ 97, .occ 104, .occ 113, .occ 116, .occ 117, .occ 121, .occ 122, .occ 124, .occ 140, .occ 144, .occ 167, .occ 208, .occ 216, .occ 246, .occ 253, .occ 260, .occ 279, .occ 280, .occ 281, .occ 290, .occ 298, .occ 301, .occ 306, .occ 317, .occ 318, .occ 321, .occ 322, .occ 327, .occ 329, .occ 330, .occ 334, .occ 335, .sumGe, .nonneg 5, .nonneg 16, .nonneg 17, .nonneg 19, .nonneg 23, .nonneg 24, .nonneg 26, .nonneg 39, .nonneg 40, .nonneg 44, .nonneg 50, .nonneg 57, .branchLe 43 (0), .branchLe 14 (0), .branchLe 1 (0), .branchLe 13 (0), .branchGe 37 (1)]

def plane426GenLeaf0003Mult : Fin 59 → Nat := ![7180236, 74036, 6630576, 8504824, 10262792, 1822824, 3773124, 571008, 2509824, 6298964, 5850936, 744060, 4008556, 5598288, 7054312, 6183412, 4071408, 1440136, 11426116, 1425400, 792538, 5027834, 624480, 447666, 1477808, 4870850, 3634680, 62892, 1275838, 812328, 713672, 2918578, 311986, 1594604, 609579, 2673059, 4195814, 2382206, 1144224, 3939341, 4732543, 22105880, 7200664, 11315348, 19525324, 515608, 3865024, 8539856, 11596624, 1167028, 3470164, 1984572, 6308804, 2512668, 11433324, 14619308, 19596056, 1046932, 63231860]

theorem plane426GenLeaf0003 (x : Fin 58 → Int)
    (hroot : plane426GenOccSys.RootHolds x)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hUB_43 : x 43 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane426GenLeaf0003Refs i).resolveCoeff plane426GenOccSys j)
    (fun i => (plane426GenLeaf0003Refs i).resolveRhs plane426GenOccSys) plane426GenLeaf0003Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane426GenLeaf0003Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 25
  · exact hroot.hOcc 48
  · exact hroot.hOcc 49
  · exact hroot.hOcc 53
  · exact hroot.hOcc 66
  · exact hroot.hOcc 76
  · exact hroot.hOcc 77
  · exact hroot.hOcc 84
  · exact hroot.hOcc 86
  · exact hroot.hOcc 97
  · exact hroot.hOcc 104
  · exact hroot.hOcc 113
  · exact hroot.hOcc 116
  · exact hroot.hOcc 117
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 124
  · exact hroot.hOcc 140
  · exact hroot.hOcc 144
  · exact hroot.hOcc 167
  · exact hroot.hOcc 208
  · exact hroot.hOcc 216
  · exact hroot.hOcc 246
  · exact hroot.hOcc 253
  · exact hroot.hOcc 260
  · exact hroot.hOcc 279
  · exact hroot.hOcc 280
  · exact hroot.hOcc 281
  · exact hroot.hOcc 290
  · exact hroot.hOcc 298
  · exact hroot.hOcc 301
  · exact hroot.hOcc 306
  · exact hroot.hOcc 317
  · exact hroot.hOcc 318
  · exact hroot.hOcc 321
  · exact hroot.hOcc 322
  · exact hroot.hOcc 327
  · exact hroot.hOcc 329
  · exact hroot.hOcc 330
  · exact hroot.hOcc 334
  · exact hroot.hOcc 335
  · change (∑ j, (-1 : Int) * x j) ≤ -plane426GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (5 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (16 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (19 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (23 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (24 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (26 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (39 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (40 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (44 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (50 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (57 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 57
  · change (∑ k, (if k = (43 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (14 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (13 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (37 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37

end QiushiMatmul
