import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0456Refs : Fin 42 → RowRef 1665 43 := ![.occ 133, .occ 138, .occ 155, .occ 163, .occ 583, .occ 599, .occ 1146, .occ 1147, .occ 1200, .occ 1225, .occ 1249, .occ 1269, .occ 1276, .occ 1283, .occ 1285, .occ 1310, .occ 1330, .occ 1337, .occ 1349, .occ 1373, .occ 1394, .occ 1402, .occ 1409, .occ 1421, .occ 1484, .occ 1536, .occ 1560, .occ 1580, .occ 1641, .sumGe, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 0 (0), .branchGe 29 (1), .branchGe 27 (1), .branchLe 8 (0), .branchLe 4 (0), .branchLe 16 (0), .branchLe 22 (0), .branchLe 1 (0), .branchLe 3 (0)]

def plane484GenLeaf0456Mult : Fin 42 → Nat := ![433, 675, 240, 126, 63, 210, 56, 49, 546, 128, 6, 303, 543, 53, 105, 805, 294, 215, 406, 727, 275, 233, 117, 209, 379, 269, 70, 53, 235, 1940, 4113, 1561, 592, 1940, 3351, 209, 1940, 1699, 1940, 316, 1454, 623]

theorem plane484GenLeaf0456 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0456Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0456Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0456Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0456Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 133
  · exact hroot.hOcc 138
  · exact hroot.hOcc 155
  · exact hroot.hOcc 163
  · exact hroot.hOcc 583
  · exact hroot.hOcc 599
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1225
  · exact hroot.hOcc 1249
  · exact hroot.hOcc 1269
  · exact hroot.hOcc 1276
  · exact hroot.hOcc 1283
  · exact hroot.hOcc 1285
  · exact hroot.hOcc 1310
  · exact hroot.hOcc 1330
  · exact hroot.hOcc 1337
  · exact hroot.hOcc 1349
  · exact hroot.hOcc 1373
  · exact hroot.hOcc 1394
  · exact hroot.hOcc 1402
  · exact hroot.hOcc 1409
  · exact hroot.hOcc 1421
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1536
  · exact hroot.hOcc 1560
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1641
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (27 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3

end QiushiMatmul
