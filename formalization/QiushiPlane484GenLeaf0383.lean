import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0383Refs : Fin 44 → RowRef 1665 43 := ![.occ 123, .occ 124, .occ 125, .occ 127, .occ 130, .occ 132, .occ 134, .occ 137, .occ 196, .occ 242, .occ 627, .occ 629, .occ 1102, .occ 1147, .occ 1170, .occ 1179, .occ 1196, .occ 1213, .occ 1228, .occ 1268, .occ 1277, .occ 1286, .occ 1292, .occ 1300, .occ 1353, .occ 1357, .occ 1458, .occ 1459, .occ 1492, .occ 1567, .occ 1573, .occ 1640, .sumGe, .nonneg 26, .nonneg 31, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchGe 23 (1), .branchGe 35 (1), .branchGe 30 (1), .branchLe 42 (0), .branchLe 8 (0), .branchLe 19 (0)]

def plane484GenLeaf0383Mult : Fin 44 → Nat := ![889, 2083, 1079, 1127, 645, 6994, 3069, 4611, 3985, 663, 3120, 2996, 2359, 3575, 425, 2613, 917, 3691, 583, 1990, 1935, 2151, 34, 184, 275, 4733, 840, 1732, 1036, 1467, 7829, 91, 13072, 2943, 7729, 12947, 12864, 6552, 39390, 14147, 23777, 9464, 11013, 12647]

theorem plane484GenLeaf0383 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0383Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0383Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0383Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0383Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 123
  · exact hroot.hOcc 124
  · exact hroot.hOcc 125
  · exact hroot.hOcc 127
  · exact hroot.hOcc 130
  · exact hroot.hOcc 132
  · exact hroot.hOcc 134
  · exact hroot.hOcc 137
  · exact hroot.hOcc 196
  · exact hroot.hOcc 242
  · exact hroot.hOcc 627
  · exact hroot.hOcc 629
  · exact hroot.hOcc 1102
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1228
  · exact hroot.hOcc 1268
  · exact hroot.hOcc 1277
  · exact hroot.hOcc 1286
  · exact hroot.hOcc 1292
  · exact hroot.hOcc 1300
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1640
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (31 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 31
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19

end QiushiMatmul
