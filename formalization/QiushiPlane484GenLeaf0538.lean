import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0538Refs : Fin 42 → RowRef 1665 43 := ![.occ 121, .occ 176, .occ 224, .occ 277, .occ 284, .occ 295, .occ 464, .occ 563, .occ 599, .occ 675, .occ 826, .occ 883, .occ 947, .occ 998, .occ 1170, .occ 1173, .occ 1188, .occ 1220, .occ 1264, .occ 1315, .occ 1367, .occ 1377, .occ 1417, .occ 1450, .occ 1483, .occ 1486, .occ 1629, .occ 1642, .occ 1646, .sumGe, .nonneg 2, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchLe 26 (0), .branchGe 30 (1), .branchLe 1 (0), .branchLe 0 (0), .branchGe 19 (1), .branchLe 6 (0), .branchLe 20 (0), .branchGe 13 (1)]

def plane484GenLeaf0538Mult : Fin 42 → Nat := ![107, 470, 65, 536, 264, 342, 12, 274, 160, 270, 221, 387, 370, 415, 135, 13, 170, 79, 65, 290, 21, 7, 135, 193, 221, 107, 21, 97, 152, 705, 42, 1252, 1478, 335, 449, 3961, 577, 478, 2057, 553, 491, 2986]

theorem plane484GenLeaf0538 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0538Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0538Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0538Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0538Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 176
  · exact hroot.hOcc 224
  · exact hroot.hOcc 277
  · exact hroot.hOcc 284
  · exact hroot.hOcc 295
  · exact hroot.hOcc 464
  · exact hroot.hOcc 563
  · exact hroot.hOcc 599
  · exact hroot.hOcc 675
  · exact hroot.hOcc 826
  · exact hroot.hOcc 883
  · exact hroot.hOcc 947
  · exact hroot.hOcc 998
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1264
  · exact hroot.hOcc 1315
  · exact hroot.hOcc 1367
  · exact hroot.hOcc 1377
  · exact hroot.hOcc 1417
  · exact hroot.hOcc 1450
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1629
  · exact hroot.hOcc 1642
  · exact hroot.hOcc 1646
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13

end QiushiMatmul
