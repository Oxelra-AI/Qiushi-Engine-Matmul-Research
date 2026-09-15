import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0168Refs : Fin 43 → RowRef 1665 43 := ![.occ 121, .occ 124, .occ 129, .occ 161, .occ 453, .occ 461, .occ 601, .occ 629, .occ 663, .occ 861, .occ 1166, .occ 1173, .occ 1215, .occ 1255, .occ 1258, .occ 1302, .occ 1315, .occ 1323, .occ 1337, .occ 1353, .occ 1373, .occ 1395, .occ 1458, .occ 1538, .occ 1549, .occ 1557, .occ 1558, .occ 1580, .occ 1608, .occ 1628, .sumGe, .nonneg 4, .nonneg 5, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchGe 7 (1), .branchLe 18 (0), .branchGe 30 (1), .branchLe 20 (0), .branchGe 33 (1), .branchGe 13 (1)]

def plane484GenLeaf0168Mult : Fin 43 → Nat := ![420, 750, 673, 717, 84, 263, 121, 479, 188, 480, 49, 644, 337, 55, 479, 257, 137, 312, 14, 93, 824, 243, 370, 353, 272, 355, 531, 93, 263, 22, 1722, 188, 1446, 1722, 972, 1883, 1078, 3059, 1290, 3214, 1191, 3424, 5571]

theorem plane484GenLeaf0168 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_33 : (1 : Int) ≤ x 33)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0168Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0168Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0168Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0168Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 124
  · exact hroot.hOcc 129
  · exact hroot.hOcc 161
  · exact hroot.hOcc 453
  · exact hroot.hOcc 461
  · exact hroot.hOcc 601
  · exact hroot.hOcc 629
  · exact hroot.hOcc 663
  · exact hroot.hOcc 861
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1255
  · exact hroot.hOcc 1258
  · exact hroot.hOcc 1302
  · exact hroot.hOcc 1315
  · exact hroot.hOcc 1323
  · exact hroot.hOcc 1337
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1373
  · exact hroot.hOcc 1395
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1538
  · exact hroot.hOcc 1549
  · exact hroot.hOcc 1557
  · exact hroot.hOcc 1558
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1628
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (33 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_33
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13

end QiushiMatmul
