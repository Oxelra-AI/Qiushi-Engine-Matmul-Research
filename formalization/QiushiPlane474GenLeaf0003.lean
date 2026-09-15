import QiushiPlane474GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane474GenLeaf0003Refs : Fin 61 → RowRef 146 60 := ![.occ 3, .occ 8, .occ 12, .occ 13, .occ 14, .occ 15, .occ 29, .occ 32, .occ 37, .occ 38, .occ 41, .occ 47, .occ 48, .occ 50, .occ 51, .occ 52, .occ 53, .occ 56, .occ 60, .occ 63, .occ 67, .occ 72, .occ 74, .occ 76, .occ 77, .occ 78, .occ 80, .occ 82, .occ 94, .occ 97, .occ 100, .occ 101, .occ 105, .occ 106, .occ 109, .occ 110, .occ 113, .occ 114, .occ 116, .occ 117, .occ 124, .occ 126, .occ 127, .occ 128, .occ 133, .occ 134, .occ 136, .occ 137, .occ 138, .occ 144, .occ 145, .sumGe, .nonneg 9, .nonneg 17, .nonneg 25, .nonneg 26, .nonneg 38, .nonneg 48, .nonneg 52, .branchLe 44 (0), .branchGe 43 (1)]

def plane474GenLeaf0003Mult : Fin 61 → Nat := ![2649932, 2531976, 3544068, 506328, 14077916, 3803242, 1490200, 2620200, 8390296, 213240, 1713260, 4946562, 4084948, 3870044, 3621270, 2730, 6815466, 4021626, 150590, 3924800, 553440, 3188354, 770562, 2231430, 5377492, 1273108, 3398754, 1126998, 1073780, 93826, 2591594, 1359503, 496832, 120270, 3350297, 4384157, 2949930, 4053480, 1140283, 2588679, 516717, 3608816, 1760329, 972418, 862414, 825699, 1263232, 326775, 2866087, 354866, 44081, 16332899, 7440364, 3160660, 4955202, 3861976, 3466272, 643702, 2407956, 12701328, 50726742]

theorem plane474GenLeaf0003 (x : Fin 60 → Int)
    (hroot : plane474GenOccSys.RootHolds x)
    (hLB_43 : (1 : Int) ≤ x 43)
    (hUB_44 : x 44 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane474GenLeaf0003Refs i).resolveCoeff plane474GenOccSys j)
    (fun i => (plane474GenLeaf0003Refs i).resolveRhs plane474GenOccSys) plane474GenLeaf0003Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane474GenLeaf0003Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 3
  · exact hroot.hOcc 8
  · exact hroot.hOcc 12
  · exact hroot.hOcc 13
  · exact hroot.hOcc 14
  · exact hroot.hOcc 15
  · exact hroot.hOcc 29
  · exact hroot.hOcc 32
  · exact hroot.hOcc 37
  · exact hroot.hOcc 38
  · exact hroot.hOcc 41
  · exact hroot.hOcc 47
  · exact hroot.hOcc 48
  · exact hroot.hOcc 50
  · exact hroot.hOcc 51
  · exact hroot.hOcc 52
  · exact hroot.hOcc 53
  · exact hroot.hOcc 56
  · exact hroot.hOcc 60
  · exact hroot.hOcc 63
  · exact hroot.hOcc 67
  · exact hroot.hOcc 72
  · exact hroot.hOcc 74
  · exact hroot.hOcc 76
  · exact hroot.hOcc 77
  · exact hroot.hOcc 78
  · exact hroot.hOcc 80
  · exact hroot.hOcc 82
  · exact hroot.hOcc 94
  · exact hroot.hOcc 97
  · exact hroot.hOcc 100
  · exact hroot.hOcc 101
  · exact hroot.hOcc 105
  · exact hroot.hOcc 106
  · exact hroot.hOcc 109
  · exact hroot.hOcc 110
  · exact hroot.hOcc 113
  · exact hroot.hOcc 114
  · exact hroot.hOcc 116
  · exact hroot.hOcc 117
  · exact hroot.hOcc 124
  · exact hroot.hOcc 126
  · exact hroot.hOcc 127
  · exact hroot.hOcc 128
  · exact hroot.hOcc 133
  · exact hroot.hOcc 134
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 144
  · exact hroot.hOcc 145
  · change (∑ j, (-1 : Int) * x j) ≤ -plane474GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (9 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 9
  · change (∑ k, (if k = (17 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (25 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (26 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (38 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (48 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (52 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (44 : Fin 60) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (43 : Fin 60) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_43

end QiushiMatmul
