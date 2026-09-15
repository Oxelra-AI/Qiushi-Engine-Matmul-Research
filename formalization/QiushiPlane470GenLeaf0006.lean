import QiushiPlane470GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane470GenLeaf0006Refs : Fin 64 → RowRef 232 63 := ![.occ 20, .occ 36, .occ 37, .occ 54, .occ 55, .occ 56, .occ 57, .occ 58, .occ 59, .occ 60, .occ 65, .occ 71, .occ 73, .occ 74, .occ 80, .occ 86, .occ 87, .occ 88, .occ 97, .occ 98, .occ 103, .occ 106, .occ 109, .occ 110, .occ 111, .occ 113, .occ 114, .occ 120, .occ 137, .occ 148, .occ 150, .occ 153, .occ 159, .occ 174, .occ 186, .occ 188, .occ 190, .occ 191, .occ 198, .occ 199, .occ 201, .occ 209, .occ 214, .occ 215, .occ 216, .occ 224, .occ 225, .sumGe, .nonneg 3, .nonneg 8, .nonneg 10, .nonneg 21, .nonneg 24, .nonneg 29, .nonneg 32, .nonneg 42, .nonneg 43, .nonneg 45, .nonneg 51, .nonneg 54, .nonneg 55, .nonneg 59, .branchLe 12 (0), .branchGe 60 (1)]

def plane470GenLeaf0006Mult : Fin 64 → Nat := ![2771, 2793, 3536, 316, 6793, 10928, 15346, 23127, 8508, 23629, 4436, 1451, 1496, 3578, 5074, 771, 1257, 3358, 1958, 1749, 8572, 4806, 32742, 11704, 18359, 13008, 7678, 7930, 889, 15066, 4576, 1194, 1998, 900, 639, 5082, 247, 8224, 8054, 99, 2288, 7099, 10281, 5729, 460, 5214, 6113, 35737, 2822, 18888, 4634, 5959, 4295, 1538, 14841, 2841, 1295, 1349, 16540, 535, 6506, 2004, 17943, 215763]

theorem plane470GenLeaf0006 (x : Fin 63 → Int)
    (hroot : plane470GenOccSys.RootHolds x)
    (hLB_60 : (1 : Int) ≤ x 60)
    (hUB_12 : x 12 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane470GenLeaf0006Refs i).resolveCoeff plane470GenOccSys j)
    (fun i => (plane470GenLeaf0006Refs i).resolveRhs plane470GenOccSys) plane470GenLeaf0006Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane470GenLeaf0006Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 20
  · exact hroot.hOcc 36
  · exact hroot.hOcc 37
  · exact hroot.hOcc 54
  · exact hroot.hOcc 55
  · exact hroot.hOcc 56
  · exact hroot.hOcc 57
  · exact hroot.hOcc 58
  · exact hroot.hOcc 59
  · exact hroot.hOcc 60
  · exact hroot.hOcc 65
  · exact hroot.hOcc 71
  · exact hroot.hOcc 73
  · exact hroot.hOcc 74
  · exact hroot.hOcc 80
  · exact hroot.hOcc 86
  · exact hroot.hOcc 87
  · exact hroot.hOcc 88
  · exact hroot.hOcc 97
  · exact hroot.hOcc 98
  · exact hroot.hOcc 103
  · exact hroot.hOcc 106
  · exact hroot.hOcc 109
  · exact hroot.hOcc 110
  · exact hroot.hOcc 111
  · exact hroot.hOcc 113
  · exact hroot.hOcc 114
  · exact hroot.hOcc 120
  · exact hroot.hOcc 137
  · exact hroot.hOcc 148
  · exact hroot.hOcc 150
  · exact hroot.hOcc 153
  · exact hroot.hOcc 159
  · exact hroot.hOcc 174
  · exact hroot.hOcc 186
  · exact hroot.hOcc 188
  · exact hroot.hOcc 190
  · exact hroot.hOcc 191
  · exact hroot.hOcc 198
  · exact hroot.hOcc 199
  · exact hroot.hOcc 201
  · exact hroot.hOcc 209
  · exact hroot.hOcc 214
  · exact hroot.hOcc 215
  · exact hroot.hOcc 216
  · exact hroot.hOcc 224
  · exact hroot.hOcc 225
  · change (∑ j, (-1 : Int) * x j) ≤ -plane470GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (8 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (10 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (21 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (24 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (29 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (32 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (42 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (43 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 43
  · change (∑ k, (if k = (45 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (51 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 51
  · change (∑ k, (if k = (54 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 54
  · change (∑ k, (if k = (55 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (59 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (12 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (60 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_60

end QiushiMatmul
