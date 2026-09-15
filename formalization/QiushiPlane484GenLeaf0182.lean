import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0182Refs : Fin 44 → RowRef 1665 43 := ![.occ 130, .occ 220, .occ 234, .occ 242, .occ 248, .occ 284, .occ 390, .occ 462, .occ 470, .occ 572, .occ 631, .occ 672, .occ 1173, .occ 1234, .occ 1241, .occ 1246, .occ 1287, .occ 1289, .occ 1299, .occ 1341, .occ 1342, .occ 1353, .occ 1388, .occ 1411, .occ 1449, .occ 1505, .occ 1523, .occ 1555, .occ 1601, .occ 1602, .occ 1624, .occ 1661, .sumGe, .nonneg 10, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchGe 35 (1), .branchLe 16 (0), .branchLe 18 (0), .branchLe 1 (0), .branchLe 5 (0), .branchLe 7 (0), .branchGe 14 (1)]

def plane484GenLeaf0182Mult : Fin 44 → Nat := ![8840, 2627, 782, 9328, 10329, 3804, 11638, 1642, 673, 18587, 2300, 2111, 2651, 1076, 874, 1505, 4836, 124, 1626, 8104, 217, 1626, 1286, 11746, 294, 6632, 1138, 8183, 4546, 227, 209, 488, 18587, 1626, 9530, 18587, 84410, 86133, 719, 15064, 18587, 7633, 6632, 59350]

theorem plane484GenLeaf0182 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0182Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0182Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0182Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0182Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 130
  · exact hroot.hOcc 220
  · exact hroot.hOcc 234
  · exact hroot.hOcc 242
  · exact hroot.hOcc 248
  · exact hroot.hOcc 284
  · exact hroot.hOcc 390
  · exact hroot.hOcc 462
  · exact hroot.hOcc 470
  · exact hroot.hOcc 572
  · exact hroot.hOcc 631
  · exact hroot.hOcc 672
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1234
  · exact hroot.hOcc 1241
  · exact hroot.hOcc 1246
  · exact hroot.hOcc 1287
  · exact hroot.hOcc 1289
  · exact hroot.hOcc 1299
  · exact hroot.hOcc 1341
  · exact hroot.hOcc 1342
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1388
  · exact hroot.hOcc 1411
  · exact hroot.hOcc 1449
  · exact hroot.hOcc 1505
  · exact hroot.hOcc 1523
  · exact hroot.hOcc 1555
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1624
  · exact hroot.hOcc 1661
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14

end QiushiMatmul
