import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0507Refs : Fin 44 → RowRef 1665 43 := ![.occ 121, .occ 126, .occ 127, .occ 131, .occ 133, .occ 135, .occ 138, .occ 142, .occ 293, .occ 483, .occ 506, .occ 520, .occ 528, .occ 539, .occ 549, .occ 581, .occ 615, .occ 982, .occ 1116, .occ 1119, .occ 1190, .occ 1206, .occ 1209, .occ 1235, .occ 1238, .occ 1254, .occ 1280, .occ 1358, .occ 1397, .occ 1484, .occ 1516, .occ 1620, .sumGe, .nonneg 26, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchLe 30 (0), .branchLe 34 (0), .branchLe 8 (0), .branchLe 33 (0), .branchLe 5 (0), .branchGe 41 (1), .branchLe 42 (0)]

def plane484GenLeaf0507Mult : Fin 44 → Nat := ![1612, 4138, 1526, 2600, 2037, 877, 5709, 2058, 6760, 3830, 1368, 1478, 3882, 6176, 6590, 4313, 188, 2456, 904, 174, 152, 1286, 1494, 1920, 36, 2094, 3004, 6090, 240, 1218, 2370, 428, 12268, 2370, 39560, 19528, 2370, 12116, 10982, 10982, 12268, 7208, 27166, 10810]

theorem plane484GenLeaf0507 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_41 : (1 : Int) ≤ x 41)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0507Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0507Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0507Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0507Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 126
  · exact hroot.hOcc 127
  · exact hroot.hOcc 131
  · exact hroot.hOcc 133
  · exact hroot.hOcc 135
  · exact hroot.hOcc 138
  · exact hroot.hOcc 142
  · exact hroot.hOcc 293
  · exact hroot.hOcc 483
  · exact hroot.hOcc 506
  · exact hroot.hOcc 520
  · exact hroot.hOcc 528
  · exact hroot.hOcc 539
  · exact hroot.hOcc 549
  · exact hroot.hOcc 581
  · exact hroot.hOcc 615
  · exact hroot.hOcc 982
  · exact hroot.hOcc 1116
  · exact hroot.hOcc 1119
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1209
  · exact hroot.hOcc 1235
  · exact hroot.hOcc 1238
  · exact hroot.hOcc 1254
  · exact hroot.hOcc 1280
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1397
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1516
  · exact hroot.hOcc 1620
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (33 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (41 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_41
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42

end QiushiMatmul
