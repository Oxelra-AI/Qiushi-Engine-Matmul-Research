import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0137Refs : Fin 42 → RowRef 1665 43 := ![.occ 130, .occ 137, .occ 237, .occ 271, .occ 275, .occ 344, .occ 402, .occ 681, .occ 724, .occ 1082, .occ 1168, .occ 1172, .occ 1223, .occ 1232, .occ 1255, .occ 1322, .occ 1381, .occ 1421, .occ 1504, .occ 1518, .occ 1543, .occ 1557, .occ 1603, .occ 1609, .occ 1618, .occ 1622, .occ 1652, .occ 1660, .sumGe, .nonneg 17, .nonneg 22, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 39 (0), .branchGe 32 (1), .branchGe 37 (1), .branchLe 1 (0), .branchLe 24 (0), .branchGe 21 (1)]

def plane484GenLeaf0137Mult : Fin 42 → Nat := ![348, 900, 25, 553, 760, 1190, 29, 333, 1203, 228, 60, 982, 372, 937, 479, 507, 164, 481, 1499, 100, 1609, 181, 552, 295, 272, 186, 162, 403, 3098, 720, 231, 2119, 2198, 4056, 3098, 2640, 2826, 8411, 4615, 2936, 1844, 2953]

theorem plane484GenLeaf0137 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0137Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0137Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0137Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0137Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 130
  · exact hroot.hOcc 137
  · exact hroot.hOcc 237
  · exact hroot.hOcc 271
  · exact hroot.hOcc 275
  · exact hroot.hOcc 344
  · exact hroot.hOcc 402
  · exact hroot.hOcc 681
  · exact hroot.hOcc 724
  · exact hroot.hOcc 1082
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1223
  · exact hroot.hOcc 1232
  · exact hroot.hOcc 1255
  · exact hroot.hOcc 1322
  · exact hroot.hOcc 1381
  · exact hroot.hOcc 1421
  · exact hroot.hOcc 1504
  · exact hroot.hOcc 1518
  · exact hroot.hOcc 1543
  · exact hroot.hOcc 1557
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1618
  · exact hroot.hOcc 1622
  · exact hroot.hOcc 1652
  · exact hroot.hOcc 1660
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (32 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21

end QiushiMatmul
