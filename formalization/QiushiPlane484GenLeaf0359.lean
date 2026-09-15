import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0359Refs : Fin 44 → RowRef 1665 43 := ![.occ 123, .occ 125, .occ 132, .occ 134, .occ 138, .occ 290, .occ 669, .occ 1017, .occ 1078, .occ 1146, .occ 1147, .occ 1174, .occ 1188, .occ 1196, .occ 1200, .occ 1228, .occ 1256, .occ 1295, .occ 1370, .occ 1389, .occ 1396, .occ 1399, .occ 1471, .occ 1484, .occ 1496, .occ 1503, .occ 1521, .occ 1567, .occ 1610, .occ 1646, .occ 1653, .sumGe, .nonneg 15, .nonneg 16, .nonneg 22, .nonneg 26, .branchGe 2 (1), .branchLe 7 (0), .branchGe 23 (1), .branchLe 35 (0), .branchLe 3 (0), .branchLe 24 (0), .branchGe 18 (1), .branchLe 25 (0)]

def plane484GenLeaf0359Mult : Fin 44 → Nat := ![4279, 4659, 16636, 16636, 19560, 2422, 424, 716, 4049, 2691, 492, 508, 2133, 2756, 7378, 202, 6583, 2852, 2354, 1046, 2264, 922, 4512, 4447, 3513, 1522, 6110, 1376, 2902, 2400, 304, 21960, 13958, 3640, 57364, 6696, 33724, 15540, 67370, 14000, 11896, 3802, 81190, 5020]

theorem plane484GenLeaf0359 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0359Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0359Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0359Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0359Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 123
  · exact hroot.hOcc 125
  · exact hroot.hOcc 132
  · exact hroot.hOcc 134
  · exact hroot.hOcc 138
  · exact hroot.hOcc 290
  · exact hroot.hOcc 669
  · exact hroot.hOcc 1017
  · exact hroot.hOcc 1078
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1228
  · exact hroot.hOcc 1256
  · exact hroot.hOcc 1295
  · exact hroot.hOcc 1370
  · exact hroot.hOcc 1389
  · exact hroot.hOcc 1396
  · exact hroot.hOcc 1399
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1503
  · exact hroot.hOcc 1521
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1646
  · exact hroot.hOcc 1653
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25

end QiushiMatmul
