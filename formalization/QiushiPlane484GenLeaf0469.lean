import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0469Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 123, .occ 125, .occ 130, .occ 131, .occ 132, .occ 138, .occ 142, .occ 163, .occ 500, .occ 687, .occ 769, .occ 1046, .occ 1156, .occ 1158, .occ 1173, .occ 1174, .occ 1187, .occ 1190, .occ 1205, .occ 1215, .occ 1255, .occ 1335, .occ 1389, .occ 1467, .occ 1503, .occ 1535, .occ 1580, .occ 1615, .sumGe, .nonneg 10, .nonneg 22, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchGe 0 (1), .branchLe 19 (0), .branchLe 25 (0), .branchLe 3 (0), .branchLe 38 (0), .branchLe 20 (0), .branchLe 27 (0), .branchLe 34 (0), .branchGe 9 (1)]

def plane484GenLeaf0469Mult : Fin 44 → Nat := ![1297, 615, 1491, 1487, 576, 1256, 971, 606, 122, 188, 1000, 1976, 21, 481, 659, 41, 826, 357, 122, 905, 768, 292, 84, 753, 520, 127, 109, 537, 286, 3556, 425, 265, 3676, 1951, 2101, 3133, 1568, 2469, 1168, 2788, 2980, 2750, 2730, 6998]

theorem plane484GenLeaf0469 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0469Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0469Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0469Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0469Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 123
  · exact hroot.hOcc 125
  · exact hroot.hOcc 130
  · exact hroot.hOcc 131
  · exact hroot.hOcc 132
  · exact hroot.hOcc 138
  · exact hroot.hOcc 142
  · exact hroot.hOcc 163
  · exact hroot.hOcc 500
  · exact hroot.hOcc 687
  · exact hroot.hOcc 769
  · exact hroot.hOcc 1046
  · exact hroot.hOcc 1156
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1255
  · exact hroot.hOcc 1335
  · exact hroot.hOcc 1389
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1503
  · exact hroot.hOcc 1535
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1615
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
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
  · change (∑ k, (if k = (9 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9

end QiushiMatmul
