import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0072Refs : Fin 44 → RowRef 1665 43 := ![.occ 139, .occ 183, .occ 628, .occ 630, .occ 712, .occ 738, .occ 757, .occ 1172, .occ 1191, .occ 1233, .occ 1253, .occ 1388, .occ 1392, .occ 1397, .occ 1422, .occ 1432, .occ 1438, .occ 1441, .occ 1458, .occ 1459, .occ 1470, .occ 1472, .occ 1506, .occ 1602, .occ 1610, .occ 1624, .occ 1626, .occ 1630, .occ 1644, .occ 1650, .occ 1659, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchGe 13 (1), .branchGe 42 (1), .branchLe 9 (0), .branchLe 20 (0), .branchLe 7 (0), .branchLe 8 (0), .branchLe 3 (0), .branchGe 27 (1)]

def plane484GenLeaf0072Mult : Fin 44 → Nat := ![4724, 21123, 18502, 825, 15816, 4724, 39135, 30560, 6245, 2744, 3765, 19796, 3904, 10319, 4519, 1870, 12158, 8998, 34003, 17428, 2876, 1309, 3753, 6916, 28469, 10319, 6998, 16371, 4986, 14514, 7963, 91225, 65021, 79994, 91225, 51790, 103841, 145349, 63621, 67938, 80906, 20493, 59426, 199938]

theorem plane484GenLeaf0072 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0072Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0072Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0072Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0072Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 139
  · exact hroot.hOcc 183
  · exact hroot.hOcc 628
  · exact hroot.hOcc 630
  · exact hroot.hOcc 712
  · exact hroot.hOcc 738
  · exact hroot.hOcc 757
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1233
  · exact hroot.hOcc 1253
  · exact hroot.hOcc 1388
  · exact hroot.hOcc 1392
  · exact hroot.hOcc 1397
  · exact hroot.hOcc 1422
  · exact hroot.hOcc 1432
  · exact hroot.hOcc 1438
  · exact hroot.hOcc 1441
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1506
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1624
  · exact hroot.hOcc 1626
  · exact hroot.hOcc 1630
  · exact hroot.hOcc 1644
  · exact hroot.hOcc 1650
  · exact hroot.hOcc 1659
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
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (27 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27

end QiushiMatmul
