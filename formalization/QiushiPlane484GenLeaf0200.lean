import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0200Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 122, .occ 127, .occ 128, .occ 132, .occ 133, .occ 140, .occ 201, .occ 216, .occ 220, .occ 224, .occ 279, .occ 388, .occ 708, .occ 760, .occ 1122, .occ 1140, .occ 1166, .occ 1170, .occ 1196, .occ 1214, .occ 1230, .occ 1353, .occ 1439, .occ 1472, .occ 1488, .occ 1511, .occ 1597, .occ 1607, .occ 1632, .occ 1662, .sumGe, .nonneg 15, .nonneg 19, .nonneg 22, .branchLe 2 (0), .branchGe 29 (1), .branchGe 35 (1), .branchLe 16 (0), .branchLe 18 (0), .branchGe 1 (1), .branchGe 21 (1), .branchLe 31 (0), .branchLe 33 (0)]

def plane484GenLeaf0200Mult : Fin 44 → Nat := ![35, 479, 41, 190, 256, 1022, 188, 36, 102, 310, 160, 252, 568, 271, 36, 18, 503, 44, 117, 116, 374, 126, 443, 144, 104, 278, 18, 327, 102, 604, 198, 1466, 86, 708, 122, 1054, 1858, 1976, 520, 606, 2366, 2958, 1466, 1144]

theorem plane484GenLeaf0200 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0200Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0200Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0200Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0200Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 122
  · exact hroot.hOcc 127
  · exact hroot.hOcc 128
  · exact hroot.hOcc 132
  · exact hroot.hOcc 133
  · exact hroot.hOcc 140
  · exact hroot.hOcc 201
  · exact hroot.hOcc 216
  · exact hroot.hOcc 220
  · exact hroot.hOcc 224
  · exact hroot.hOcc 279
  · exact hroot.hOcc 388
  · exact hroot.hOcc 708
  · exact hroot.hOcc 760
  · exact hroot.hOcc 1122
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1230
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1439
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1511
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1632
  · exact hroot.hOcc 1662
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21
  · change (∑ k, (if k = (31 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (33 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33

end QiushiMatmul
