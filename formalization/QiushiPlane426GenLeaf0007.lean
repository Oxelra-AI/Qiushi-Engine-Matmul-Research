import QiushiPlane426GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane426GenLeaf0007Refs : Fin 59 → RowRef 340 58 := ![.occ 5, .occ 35, .occ 43, .occ 44, .occ 71, .occ 86, .occ 88, .occ 99, .occ 102, .occ 104, .occ 111, .occ 116, .occ 117, .occ 121, .occ 123, .occ 124, .occ 132, .occ 138, .occ 141, .occ 144, .occ 146, .occ 152, .occ 185, .occ 194, .occ 206, .occ 208, .occ 222, .occ 224, .occ 227, .occ 229, .occ 235, .occ 239, .occ 241, .occ 278, .occ 280, .occ 290, .occ 295, .occ 311, .occ 323, .occ 327, .occ 333, .sumGe, .nonneg 6, .nonneg 16, .nonneg 17, .nonneg 19, .nonneg 24, .nonneg 26, .nonneg 33, .nonneg 40, .nonneg 43, .nonneg 47, .nonneg 50, .branchLe 14 (0), .branchGe 1 (1), .branchLe 35 (0), .branchLe 4 (0), .branchLe 10 (0), .branchGe 34 (1)]

def plane426GenLeaf0007Mult : Fin 59 → Nat := ![1584120, 13872, 35948, 369123, 32730, 941176, 1716336, 991212, 193317, 2108353, 254996, 797666, 2144, 26428, 301320, 760006, 1093435, 1640300, 453190, 1244119, 171006, 648039, 481098, 35360, 1622, 1497882, 27239, 10360, 87018, 646566, 11751, 99314, 680962, 521958, 208362, 678907, 417201, 444163, 323049, 245300, 148772, 3213822, 238178, 4088340, 5513603, 1457534, 4801, 2089004, 271928, 499824, 192304, 660484, 281957, 3018361, 3114687, 2305044, 2469462, 3114508, 2727286]

theorem plane426GenLeaf0007 (x : Fin 58 → Int)
    (hroot : plane426GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hUB_43 : x 43 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane426GenLeaf0007Refs i).resolveCoeff plane426GenOccSys j)
    (fun i => (plane426GenLeaf0007Refs i).resolveRhs plane426GenOccSys) plane426GenLeaf0007Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane426GenLeaf0007Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · exact hroot.hOcc 35
  · exact hroot.hOcc 43
  · exact hroot.hOcc 44
  · exact hroot.hOcc 71
  · exact hroot.hOcc 86
  · exact hroot.hOcc 88
  · exact hroot.hOcc 99
  · exact hroot.hOcc 102
  · exact hroot.hOcc 104
  · exact hroot.hOcc 111
  · exact hroot.hOcc 116
  · exact hroot.hOcc 117
  · exact hroot.hOcc 121
  · exact hroot.hOcc 123
  · exact hroot.hOcc 124
  · exact hroot.hOcc 132
  · exact hroot.hOcc 138
  · exact hroot.hOcc 141
  · exact hroot.hOcc 144
  · exact hroot.hOcc 146
  · exact hroot.hOcc 152
  · exact hroot.hOcc 185
  · exact hroot.hOcc 194
  · exact hroot.hOcc 206
  · exact hroot.hOcc 208
  · exact hroot.hOcc 222
  · exact hroot.hOcc 224
  · exact hroot.hOcc 227
  · exact hroot.hOcc 229
  · exact hroot.hOcc 235
  · exact hroot.hOcc 239
  · exact hroot.hOcc 241
  · exact hroot.hOcc 278
  · exact hroot.hOcc 280
  · exact hroot.hOcc 290
  · exact hroot.hOcc 295
  · exact hroot.hOcc 311
  · exact hroot.hOcc 323
  · exact hroot.hOcc 327
  · exact hroot.hOcc 333
  · change (∑ j, (-1 : Int) * x j) ≤ -plane426GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (16 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (19 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (24 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (26 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (33 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (40 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (43 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 43
  · change (∑ k, (if k = (47 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (50 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (14 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (35 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (4 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (10 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (34 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34

end QiushiMatmul
