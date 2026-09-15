import QiushiPlane475GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane475GenLeaf0000Refs : Fin 57 → RowRef 126 56 := ![.occ 14, .occ 20, .occ 22, .occ 25, .occ 27, .occ 30, .occ 31, .occ 36, .occ 37, .occ 39, .occ 41, .occ 43, .occ 44, .occ 47, .occ 49, .occ 51, .occ 53, .occ 56, .occ 57, .occ 58, .occ 59, .occ 60, .occ 63, .occ 65, .occ 67, .occ 68, .occ 69, .occ 71, .occ 72, .occ 73, .occ 77, .occ 78, .occ 79, .occ 80, .occ 82, .occ 83, .occ 87, .occ 88, .occ 90, .occ 92, .occ 96, .occ 105, .occ 107, .occ 109, .occ 118, .occ 119, .occ 120, .occ 121, .occ 125, .sumGe, .nonneg 24, .nonneg 35, .nonneg 44, .nonneg 48, .nonneg 52, .branchLe 34 (0), .branchLe 2 (0)]

def plane475GenLeaf0000Mult : Fin 57 → Nat := ![2888731, 216855, 2199775, 318414, 645217, 624490, 2085129, 331099, 557821, 221548, 867442, 596983, 305910, 357491, 4490776, 1767090, 397207, 1535957, 127463, 974363, 1258077, 2472735, 391387, 3500764, 575377, 1810812, 2900828, 850551, 1488374, 4418120, 2495095, 403569, 1734759, 154374, 92882, 1455317, 360944, 212457, 1468719, 339166, 2036876, 892386, 474485, 472053, 808936, 1124800, 960261, 392257, 866375, 8184891, 4405031, 1728360, 1646143, 102051, 802347, 8184891, 7878981]

theorem plane475GenLeaf0000 (x : Fin 56 → Int)
    (hroot : plane475GenOccSys.RootHolds x)
    (hUB_34 : x 34 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane475GenLeaf0000Refs i).resolveCoeff plane475GenOccSys j)
    (fun i => (plane475GenLeaf0000Refs i).resolveRhs plane475GenOccSys) plane475GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane475GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 14
  · exact hroot.hOcc 20
  · exact hroot.hOcc 22
  · exact hroot.hOcc 25
  · exact hroot.hOcc 27
  · exact hroot.hOcc 30
  · exact hroot.hOcc 31
  · exact hroot.hOcc 36
  · exact hroot.hOcc 37
  · exact hroot.hOcc 39
  · exact hroot.hOcc 41
  · exact hroot.hOcc 43
  · exact hroot.hOcc 44
  · exact hroot.hOcc 47
  · exact hroot.hOcc 49
  · exact hroot.hOcc 51
  · exact hroot.hOcc 53
  · exact hroot.hOcc 56
  · exact hroot.hOcc 57
  · exact hroot.hOcc 58
  · exact hroot.hOcc 59
  · exact hroot.hOcc 60
  · exact hroot.hOcc 63
  · exact hroot.hOcc 65
  · exact hroot.hOcc 67
  · exact hroot.hOcc 68
  · exact hroot.hOcc 69
  · exact hroot.hOcc 71
  · exact hroot.hOcc 72
  · exact hroot.hOcc 73
  · exact hroot.hOcc 77
  · exact hroot.hOcc 78
  · exact hroot.hOcc 79
  · exact hroot.hOcc 80
  · exact hroot.hOcc 82
  · exact hroot.hOcc 83
  · exact hroot.hOcc 87
  · exact hroot.hOcc 88
  · exact hroot.hOcc 90
  · exact hroot.hOcc 92
  · exact hroot.hOcc 96
  · exact hroot.hOcc 105
  · exact hroot.hOcc 107
  · exact hroot.hOcc 109
  · exact hroot.hOcc 118
  · exact hroot.hOcc 119
  · exact hroot.hOcc 120
  · exact hroot.hOcc 121
  · exact hroot.hOcc 125
  · change (∑ j, (-1 : Int) * x j) ≤ -plane475GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (24 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (35 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 35
  · change (∑ k, (if k = (44 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (48 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (52 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (34 : Fin 56) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (2 : Fin 56) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2

end QiushiMatmul
