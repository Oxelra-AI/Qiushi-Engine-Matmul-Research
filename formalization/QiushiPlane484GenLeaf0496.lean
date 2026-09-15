import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0496Refs : Fin 44 → RowRef 1665 43 := ![.occ 124, .occ 126, .occ 133, .occ 142, .occ 186, .occ 283, .occ 330, .occ 439, .occ 504, .occ 517, .occ 555, .occ 586, .occ 595, .occ 654, .occ 733, .occ 801, .occ 858, .occ 1181, .occ 1206, .occ 1374, .occ 1402, .occ 1405, .occ 1415, .occ 1424, .occ 1432, .occ 1590, .occ 1608, .occ 1610, .occ 1615, .occ 1628, .occ 1642, .occ 1655, .occ 1659, .sumGe, .nonneg 2, .nonneg 13, .branchGe 15 (1), .branchLe 35 (0), .branchGe 7 (1), .branchLe 32 (0), .branchLe 14 (0), .branchLe 36 (0), .branchGe 10 (1), .branchGe 28 (1)]

def plane484GenLeaf0496Mult : Fin 44 → Nat := ![940, 845, 373, 743, 558, 4, 547, 881, 191, 66, 306, 4, 1182, 172, 237, 90, 221, 102, 11, 19, 492, 14, 99, 79, 175, 932, 33, 71, 28, 85, 284, 19, 2, 1424, 968, 3, 4477, 1413, 2902, 1377, 463, 1424, 1982, 3587]

theorem plane484GenLeaf0496 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0496Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0496Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0496Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0496Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 124
  · exact hroot.hOcc 126
  · exact hroot.hOcc 133
  · exact hroot.hOcc 142
  · exact hroot.hOcc 186
  · exact hroot.hOcc 283
  · exact hroot.hOcc 330
  · exact hroot.hOcc 439
  · exact hroot.hOcc 504
  · exact hroot.hOcc 517
  · exact hroot.hOcc 555
  · exact hroot.hOcc 586
  · exact hroot.hOcc 595
  · exact hroot.hOcc 654
  · exact hroot.hOcc 733
  · exact hroot.hOcc 801
  · exact hroot.hOcc 858
  · exact hroot.hOcc 1181
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1374
  · exact hroot.hOcc 1402
  · exact hroot.hOcc 1405
  · exact hroot.hOcc 1415
  · exact hroot.hOcc 1424
  · exact hroot.hOcc 1432
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1628
  · exact hroot.hOcc 1642
  · exact hroot.hOcc 1655
  · exact hroot.hOcc 1659
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28

end QiushiMatmul
