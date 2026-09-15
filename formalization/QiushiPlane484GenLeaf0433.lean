import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0433Refs : Fin 40 → RowRef 1665 43 := ![.occ 105, .occ 135, .occ 514, .occ 539, .occ 581, .occ 610, .occ 654, .occ 691, .occ 966, .occ 1043, .occ 1046, .occ 1075, .occ 1188, .occ 1190, .occ 1191, .occ 1250, .occ 1311, .occ 1318, .occ 1350, .occ 1358, .occ 1385, .occ 1393, .occ 1454, .occ 1470, .occ 1483, .occ 1520, .occ 1599, .occ 1615, .occ 1630, .sumGe, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 0 (0), .branchLe 29 (0), .branchLe 23 (0), .branchLe 19 (0), .branchGe 40 (1), .branchLe 6 (0), .branchGe 41 (1)]

def plane484GenLeaf0433Mult : Fin 40 → Nat := ![3823, 1805, 768, 277, 1975, 2055, 3594, 977, 481, 420, 506, 8, 884, 1774, 640, 144, 582, 2064, 48, 298, 1366, 1, 609, 1134, 188, 1267, 1280, 165, 902, 5291, 16093, 5103, 5291, 4828, 5291, 5291, 5291, 6903, 4784, 9277]

theorem plane484GenLeaf0433 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_40 : (1 : Int) ≤ x 40)
    (hLB_41 : (1 : Int) ≤ x 41)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0433Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0433Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0433Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0433Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 105
  · exact hroot.hOcc 135
  · exact hroot.hOcc 514
  · exact hroot.hOcc 539
  · exact hroot.hOcc 581
  · exact hroot.hOcc 610
  · exact hroot.hOcc 654
  · exact hroot.hOcc 691
  · exact hroot.hOcc 966
  · exact hroot.hOcc 1043
  · exact hroot.hOcc 1046
  · exact hroot.hOcc 1075
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1250
  · exact hroot.hOcc 1311
  · exact hroot.hOcc 1318
  · exact hroot.hOcc 1350
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1385
  · exact hroot.hOcc 1393
  · exact hroot.hOcc 1454
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1520
  · exact hroot.hOcc 1599
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1630
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (40 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_40
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (41 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_41

end QiushiMatmul
