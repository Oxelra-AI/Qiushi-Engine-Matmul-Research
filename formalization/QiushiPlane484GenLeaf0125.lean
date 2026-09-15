import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0125Refs : Fin 44 → RowRef 1665 43 := ![.occ 130, .occ 537, .occ 729, .occ 750, .occ 764, .occ 801, .occ 860, .occ 1215, .occ 1223, .occ 1224, .occ 1240, .occ 1290, .occ 1315, .occ 1395, .occ 1407, .occ 1415, .occ 1419, .occ 1427, .occ 1428, .occ 1457, .occ 1462, .occ 1470, .occ 1477, .occ 1542, .occ 1558, .occ 1602, .occ 1603, .occ 1608, .occ 1619, .occ 1632, .occ 1661, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 39 (0), .branchLe 32 (0), .branchGe 28 (1), .branchLe 6 (0), .branchGe 42 (1), .branchLe 10 (0), .branchLe 5 (0)]

def plane484GenLeaf0125Mult : Fin 44 → Nat := ![1325, 7274, 49937, 75666, 20100, 10095, 36114, 37615, 14037, 9038, 667, 46850, 13242, 10250, 8639, 6558, 23424, 33780, 26960, 20505, 2739, 682, 26530, 900, 1373, 56295, 26714, 55498, 19968, 63560, 27945, 187745, 167777, 187745, 222961, 124185, 59381, 73523, 185006, 225429, 78766, 358132, 137825, 187745]

theorem plane484GenLeaf0125 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0125Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0125Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0125Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0125Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 130
  · exact hroot.hOcc 537
  · exact hroot.hOcc 729
  · exact hroot.hOcc 750
  · exact hroot.hOcc 764
  · exact hroot.hOcc 801
  · exact hroot.hOcc 860
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1223
  · exact hroot.hOcc 1224
  · exact hroot.hOcc 1240
  · exact hroot.hOcc 1290
  · exact hroot.hOcc 1315
  · exact hroot.hOcc 1395
  · exact hroot.hOcc 1407
  · exact hroot.hOcc 1415
  · exact hroot.hOcc 1419
  · exact hroot.hOcc 1427
  · exact hroot.hOcc 1428
  · exact hroot.hOcc 1457
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1542
  · exact hroot.hOcc 1558
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1619
  · exact hroot.hOcc 1632
  · exact hroot.hOcc 1661
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5

end QiushiMatmul
