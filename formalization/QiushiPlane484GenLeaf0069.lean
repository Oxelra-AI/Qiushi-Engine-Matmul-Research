import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0069Refs : Fin 40 → RowRef 1665 43 := ![.occ 120, .occ 121, .occ 122, .occ 129, .occ 132, .occ 141, .occ 145, .occ 215, .occ 237, .occ 297, .occ 568, .occ 570, .occ 671, .occ 677, .occ 1113, .occ 1172, .occ 1173, .occ 1177, .occ 1190, .occ 1191, .occ 1213, .occ 1215, .occ 1220, .occ 1458, .occ 1539, .occ 1559, .occ 1580, .occ 1618, .occ 1621, .occ 1657, .sumGe, .nonneg 14, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchGe 13 (1), .branchLe 42 (0), .branchGe 0 (1), .branchGe 32 (1), .branchGe 33 (1)]

def plane484GenLeaf0069Mult : Fin 40 → Nat := ![3093, 3029, 3571, 14322, 6452, 11176, 1603, 4966, 4966, 10088, 3512, 36, 1706, 3496, 13532, 12816, 3888, 542, 702, 366, 2786, 1108, 4276, 2738, 3502, 3502, 9382, 1490, 2712, 542, 23698, 35740, 20986, 22630, 22590, 60150, 20960, 51662, 42180, 36898]

theorem plane484GenLeaf0069 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hLB_33 : (1 : Int) ≤ x 33)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0069Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0069Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0069Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0069Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 129
  · exact hroot.hOcc 132
  · exact hroot.hOcc 141
  · exact hroot.hOcc 145
  · exact hroot.hOcc 215
  · exact hroot.hOcc 237
  · exact hroot.hOcc 297
  · exact hroot.hOcc 568
  · exact hroot.hOcc 570
  · exact hroot.hOcc 671
  · exact hroot.hOcc 677
  · exact hroot.hOcc 1113
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1177
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1539
  · exact hroot.hOcc 1559
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1618
  · exact hroot.hOcc 1621
  · exact hroot.hOcc 1657
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (32 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32
  · change (∑ k, (if k = (33 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_33

end QiushiMatmul
