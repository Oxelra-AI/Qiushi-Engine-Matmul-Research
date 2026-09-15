import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0223Refs : Fin 42 → RowRef 1665 43 := ![.occ 131, .occ 137, .occ 141, .occ 201, .occ 216, .occ 323, .occ 379, .occ 488, .occ 860, .occ 1140, .occ 1174, .occ 1191, .occ 1222, .occ 1236, .occ 1254, .occ 1258, .occ 1268, .occ 1287, .occ 1328, .occ 1368, .occ 1398, .occ 1425, .occ 1426, .occ 1481, .occ 1517, .occ 1534, .occ 1539, .occ 1548, .occ 1627, .occ 1653, .sumGe, .nonneg 2, .nonneg 19, .nonneg 23, .nonneg 26, .branchLe 15 (0), .branchGe 29 (1), .branchGe 35 (1), .branchGe 16 (1), .branchGe 37 (1), .branchGe 17 (1), .branchGe 20 (1)]

def plane484GenLeaf0223Mult : Fin 42 → Nat := ![922, 1286, 364, 166, 790, 894, 646, 12, 296, 178, 189, 192, 465, 178, 436, 75, 296, 31, 36, 84, 167, 64, 393, 392, 94, 207, 190, 14, 186, 437, 1286, 584, 178, 3237, 1331, 178, 3080, 4039, 5023, 1487, 2821, 5536]

theorem plane484GenLeaf0223 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0223Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0223Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0223Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0223Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 131
  · exact hroot.hOcc 137
  · exact hroot.hOcc 141
  · exact hroot.hOcc 201
  · exact hroot.hOcc 216
  · exact hroot.hOcc 323
  · exact hroot.hOcc 379
  · exact hroot.hOcc 488
  · exact hroot.hOcc 860
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1222
  · exact hroot.hOcc 1236
  · exact hroot.hOcc 1254
  · exact hroot.hOcc 1258
  · exact hroot.hOcc 1268
  · exact hroot.hOcc 1287
  · exact hroot.hOcc 1328
  · exact hroot.hOcc 1368
  · exact hroot.hOcc 1398
  · exact hroot.hOcc 1425
  · exact hroot.hOcc 1426
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1517
  · exact hroot.hOcc 1534
  · exact hroot.hOcc 1539
  · exact hroot.hOcc 1548
  · exact hroot.hOcc 1627
  · exact hroot.hOcc 1653
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20

end QiushiMatmul
