import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0074Refs : Fin 44 → RowRef 1665 43 := ![.occ 122, .occ 129, .occ 132, .occ 136, .occ 256, .occ 283, .occ 385, .occ 501, .occ 547, .occ 740, .occ 1168, .occ 1172, .occ 1173, .occ 1190, .occ 1244, .occ 1303, .occ 1308, .occ 1322, .occ 1387, .occ 1414, .occ 1429, .occ 1430, .occ 1433, .occ 1435, .occ 1449, .occ 1458, .occ 1459, .occ 1522, .occ 1531, .occ 1644, .occ 1650, .occ 1651, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchGe 13 (1), .branchGe 42 (1), .branchLe 9 (0), .branchLe 20 (0), .branchLe 7 (0), .branchGe 8 (1), .branchLe 28 (0)]

def plane484GenLeaf0074Mult : Fin 44 → Nat := ![1434, 79610, 32945, 22613, 23519, 41899, 634, 4365, 7969, 44573, 34933, 8903, 2267, 12812, 18445, 6372, 29069, 9724, 13350, 3088, 1553, 43523, 23299, 2909, 24088, 31998, 5210, 12629, 11170, 131, 67374, 10109, 158658, 142177, 123102, 158658, 34299, 164142, 34933, 110782, 145461, 67878, 218592, 158527]

theorem plane484GenLeaf0074 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0074Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0074Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0074Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0074Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 122
  · exact hroot.hOcc 129
  · exact hroot.hOcc 132
  · exact hroot.hOcc 136
  · exact hroot.hOcc 256
  · exact hroot.hOcc 283
  · exact hroot.hOcc 385
  · exact hroot.hOcc 501
  · exact hroot.hOcc 547
  · exact hroot.hOcc 740
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1244
  · exact hroot.hOcc 1303
  · exact hroot.hOcc 1308
  · exact hroot.hOcc 1322
  · exact hroot.hOcc 1387
  · exact hroot.hOcc 1414
  · exact hroot.hOcc 1429
  · exact hroot.hOcc 1430
  · exact hroot.hOcc 1433
  · exact hroot.hOcc 1435
  · exact hroot.hOcc 1449
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1522
  · exact hroot.hOcc 1531
  · exact hroot.hOcc 1644
  · exact hroot.hOcc 1650
  · exact hroot.hOcc 1651
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42
  · change (∑ k, (if k = (9 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28

end QiushiMatmul
