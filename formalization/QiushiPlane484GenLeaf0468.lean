import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0468Refs : Fin 44 → RowRef 1665 43 := ![.occ 96, .occ 122, .occ 129, .occ 132, .occ 142, .occ 175, .occ 180, .occ 290, .occ 325, .occ 330, .occ 581, .occ 654, .occ 762, .occ 763, .occ 1158, .occ 1190, .occ 1205, .occ 1255, .occ 1479, .occ 1481, .occ 1483, .occ 1491, .occ 1567, .occ 1580, .occ 1603, .occ 1606, .occ 1608, .occ 1610, .occ 1615, .occ 1629, .sumGe, .nonneg 22, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchGe 0 (1), .branchLe 19 (0), .branchLe 25 (0), .branchLe 3 (0), .branchLe 38 (0), .branchLe 20 (0), .branchLe 27 (0), .branchLe 34 (0), .branchLe 9 (0)]

def plane484GenLeaf0468Mult : Fin 44 → Nat := ![9084, 27362, 30100, 11388, 19859, 9952, 21836, 2940, 70027, 35367, 23596, 29232, 5223, 7159, 44896, 16796, 20832, 38438, 17258, 1017, 6790, 4087, 26143, 30777, 50140, 3043, 2437, 20053, 2618, 26871, 146696, 28314, 145774, 70118, 114159, 86097, 14431, 93442, 103168, 93710, 87733, 144078, 146696, 108925]

theorem plane484GenLeaf0468 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0468Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0468Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0468Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0468Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 96
  · exact hroot.hOcc 122
  · exact hroot.hOcc 129
  · exact hroot.hOcc 132
  · exact hroot.hOcc 142
  · exact hroot.hOcc 175
  · exact hroot.hOcc 180
  · exact hroot.hOcc 290
  · exact hroot.hOcc 325
  · exact hroot.hOcc 330
  · exact hroot.hOcc 581
  · exact hroot.hOcc 654
  · exact hroot.hOcc 762
  · exact hroot.hOcc 763
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1255
  · exact hroot.hOcc 1479
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1629
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (38 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (27 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (9 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9

end QiushiMatmul
