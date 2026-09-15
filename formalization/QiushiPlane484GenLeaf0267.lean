import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0267Refs : Fin 44 → RowRef 1665 43 := ![.occ 92, .occ 108, .occ 109, .occ 123, .occ 128, .occ 290, .occ 412, .occ 615, .occ 860, .occ 1102, .occ 1132, .occ 1134, .occ 1151, .occ 1154, .occ 1158, .occ 1159, .occ 1170, .occ 1186, .occ 1208, .occ 1220, .occ 1472, .occ 1481, .occ 1488, .occ 1492, .occ 1610, .occ 1625, .occ 1632, .occ 1640, .occ 1656, .sumGe, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchGe 29 (1), .branchLe 34 (0), .branchLe 13 (0), .branchLe 37 (0), .branchLe 10 (0), .branchLe 25 (0), .branchGe 35 (1), .branchLe 4 (0), .branchLe 36 (0)]

def plane484GenLeaf0267Mult : Fin 44 → Nat := ![2339, 389, 1425, 1622, 596, 482, 1291, 2812, 275, 60, 332, 228, 271, 2432, 338, 372, 893, 1799, 111, 946, 70, 3752, 1255, 1264, 341, 641, 864, 772, 1502, 7546, 5504, 3206, 6511, 3899, 4311, 6930, 4306, 5924, 4773, 4265, 4594, 3651, 5639, 5994]

theorem plane484GenLeaf0267 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0267Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0267Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0267Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0267Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 92
  · exact hroot.hOcc 108
  · exact hroot.hOcc 109
  · exact hroot.hOcc 123
  · exact hroot.hOcc 128
  · exact hroot.hOcc 290
  · exact hroot.hOcc 412
  · exact hroot.hOcc 615
  · exact hroot.hOcc 860
  · exact hroot.hOcc 1102
  · exact hroot.hOcc 1132
  · exact hroot.hOcc 1134
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1159
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1625
  · exact hroot.hOcc 1632
  · exact hroot.hOcc 1640
  · exact hroot.hOcc 1656
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (37 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36

end QiushiMatmul
