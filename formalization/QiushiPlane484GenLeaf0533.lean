import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0533Refs : Fin 44 → RowRef 1665 43 := ![.occ 132, .occ 212, .occ 224, .occ 326, .occ 390, .occ 398, .occ 400, .occ 471, .occ 607, .occ 1158, .occ 1160, .occ 1200, .occ 1205, .occ 1208, .occ 1256, .occ 1257, .occ 1260, .occ 1286, .occ 1317, .occ 1322, .occ 1333, .occ 1348, .occ 1430, .occ 1431, .occ 1434, .occ 1449, .occ 1455, .occ 1531, .occ 1535, .occ 1547, .occ 1615, .sumGe, .nonneg 39, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchLe 26 (0), .branchGe 30 (1), .branchLe 1 (0), .branchLe 0 (0), .branchLe 19 (0), .branchLe 2 (0), .branchLe 14 (0), .branchGe 40 (1)]

def plane484GenLeaf0533Mult : Fin 44 → Nat := ![11, 20, 72, 15, 8, 17, 33, 10, 1, 32, 23, 13, 1, 9, 6, 5, 15, 19, 32, 2, 47, 8, 2, 35, 3, 34, 23, 1, 37, 11, 1, 98, 1, 133, 209, 40, 50, 353, 88, 31, 90, 85, 85, 289]

theorem plane484GenLeaf0533 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_40 : (1 : Int) ≤ x 40)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0533Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0533Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0533Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0533Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 132
  · exact hroot.hOcc 212
  · exact hroot.hOcc 224
  · exact hroot.hOcc 326
  · exact hroot.hOcc 390
  · exact hroot.hOcc 398
  · exact hroot.hOcc 400
  · exact hroot.hOcc 471
  · exact hroot.hOcc 607
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1256
  · exact hroot.hOcc 1257
  · exact hroot.hOcc 1260
  · exact hroot.hOcc 1286
  · exact hroot.hOcc 1317
  · exact hroot.hOcc 1322
  · exact hroot.hOcc 1333
  · exact hroot.hOcc 1348
  · exact hroot.hOcc 1430
  · exact hroot.hOcc 1431
  · exact hroot.hOcc 1434
  · exact hroot.hOcc 1449
  · exact hroot.hOcc 1455
  · exact hroot.hOcc 1531
  · exact hroot.hOcc 1535
  · exact hroot.hOcc 1547
  · exact hroot.hOcc 1615
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (39 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (40 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_40

end QiushiMatmul
