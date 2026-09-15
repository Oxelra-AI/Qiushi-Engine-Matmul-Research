import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0056Refs : Fin 44 → RowRef 1665 43 := ![.occ 126, .occ 128, .occ 132, .occ 136, .occ 177, .occ 263, .occ 290, .occ 509, .occ 587, .occ 634, .occ 708, .occ 768, .occ 949, .occ 980, .occ 1168, .occ 1196, .occ 1205, .occ 1206, .occ 1239, .occ 1313, .occ 1357, .occ 1367, .occ 1398, .occ 1433, .occ 1470, .occ 1472, .occ 1487, .occ 1502, .occ 1533, .occ 1549, .occ 1552, .occ 1571, .occ 1607, .occ 1647, .sumGe, .branchLe 15 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchGe 17 (1), .branchGe 7 (1), .branchGe 10 (1), .branchLe 18 (0), .branchGe 36 (1)]

def plane484GenLeaf0056Mult : Fin 44 → Nat := ![870, 1111, 1134, 1158, 256, 157, 1274, 390, 1202, 2414, 203, 1102, 2743, 235, 374, 577, 205, 701, 1290, 266, 609, 438, 222, 16, 1358, 422, 36, 219, 349, 106, 338, 382, 203, 774, 3797, 2891, 3415, 2401, 3245, 10936, 6775, 7134, 1305, 9505]

theorem plane484GenLeaf0056 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0056Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0056Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0056Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0056Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 126
  · exact hroot.hOcc 128
  · exact hroot.hOcc 132
  · exact hroot.hOcc 136
  · exact hroot.hOcc 177
  · exact hroot.hOcc 263
  · exact hroot.hOcc 290
  · exact hroot.hOcc 509
  · exact hroot.hOcc 587
  · exact hroot.hOcc 634
  · exact hroot.hOcc 708
  · exact hroot.hOcc 768
  · exact hroot.hOcc 949
  · exact hroot.hOcc 980
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1239
  · exact hroot.hOcc 1313
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1367
  · exact hroot.hOcc 1398
  · exact hroot.hOcc 1433
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1487
  · exact hroot.hOcc 1502
  · exact hroot.hOcc 1533
  · exact hroot.hOcc 1549
  · exact hroot.hOcc 1552
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1647
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (36 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36

end QiushiMatmul
