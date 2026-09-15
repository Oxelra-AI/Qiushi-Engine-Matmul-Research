import QiushiPlane426GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane426GenLeaf0008Refs : Fin 59 → RowRef 340 58 := ![.occ 5, .occ 44, .occ 48, .occ 71, .occ 79, .occ 88, .occ 98, .occ 99, .occ 104, .occ 115, .occ 116, .occ 121, .occ 122, .occ 123, .occ 124, .occ 130, .occ 132, .occ 138, .occ 142, .occ 144, .occ 146, .occ 148, .occ 154, .occ 163, .occ 187, .occ 194, .occ 205, .occ 208, .occ 229, .occ 235, .occ 239, .occ 242, .occ 279, .occ 285, .occ 290, .occ 306, .occ 322, .occ 333, .occ 334, .occ 335, .sumGe, .nonneg 5, .nonneg 16, .nonneg 17, .nonneg 19, .nonneg 22, .nonneg 23, .nonneg 24, .nonneg 25, .nonneg 33, .nonneg 40, .nonneg 47, .branchLe 43 (0), .branchLe 14 (0), .branchGe 1 (1), .branchLe 35 (0), .branchLe 4 (0), .branchGe 10 (1), .branchLe 20 (0)]

def plane426GenLeaf0008Mult : Fin 59 → Nat := ![2209414, 209766, 319321, 1875057, 2185966, 329287, 16468, 1406164, 1784126, 330771, 2132746, 224286, 465808, 629692, 1063079, 791979, 1387218, 959043, 1495465, 975221, 79067, 452556, 53934, 207060, 334894, 1382297, 783327, 1013989, 4650, 112352, 688886, 440371, 1507040, 4724, 1135575, 706477, 26138, 117942, 1060222, 839520, 5132638, 2182806, 2759717, 11546327, 605031, 294387, 612014, 452357, 148668, 806659, 1317507, 337089, 3453847, 5132638, 1842269, 3085959, 3088816, 1317507, 5132638]

theorem plane426GenLeaf0008 (x : Fin 58 → Int)
    (hroot : plane426GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hUB_43 : x 43 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane426GenLeaf0008Refs i).resolveCoeff plane426GenOccSys j)
    (fun i => (plane426GenLeaf0008Refs i).resolveRhs plane426GenOccSys) plane426GenLeaf0008Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane426GenLeaf0008Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · exact hroot.hOcc 44
  · exact hroot.hOcc 48
  · exact hroot.hOcc 71
  · exact hroot.hOcc 79
  · exact hroot.hOcc 88
  · exact hroot.hOcc 98
  · exact hroot.hOcc 99
  · exact hroot.hOcc 104
  · exact hroot.hOcc 115
  · exact hroot.hOcc 116
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 124
  · exact hroot.hOcc 130
  · exact hroot.hOcc 132
  · exact hroot.hOcc 138
  · exact hroot.hOcc 142
  · exact hroot.hOcc 144
  · exact hroot.hOcc 146
  · exact hroot.hOcc 148
  · exact hroot.hOcc 154
  · exact hroot.hOcc 163
  · exact hroot.hOcc 187
  · exact hroot.hOcc 194
  · exact hroot.hOcc 205
  · exact hroot.hOcc 208
  · exact hroot.hOcc 229
  · exact hroot.hOcc 235
  · exact hroot.hOcc 239
  · exact hroot.hOcc 242
  · exact hroot.hOcc 279
  · exact hroot.hOcc 285
  · exact hroot.hOcc 290
  · exact hroot.hOcc 306
  · exact hroot.hOcc 322
  · exact hroot.hOcc 333
  · exact hroot.hOcc 334
  · exact hroot.hOcc 335
  · change (∑ j, (-1 : Int) * x j) ≤ -plane426GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (5 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (16 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (19 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (22 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (23 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (24 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (25 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (33 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (40 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (47 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (43 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (14 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (35 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (4 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (10 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10
  · change (∑ k, (if k = (20 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20

end QiushiMatmul
