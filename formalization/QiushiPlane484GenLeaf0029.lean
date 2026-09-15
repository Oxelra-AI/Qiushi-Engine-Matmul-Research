import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0029Refs : Fin 41 → RowRef 1665 43 := ![.occ 125, .occ 128, .occ 143, .occ 179, .occ 253, .occ 284, .occ 543, .occ 558, .occ 749, .occ 787, .occ 1173, .occ 1186, .occ 1213, .occ 1220, .occ 1368, .occ 1369, .occ 1388, .occ 1392, .occ 1400, .occ 1412, .occ 1422, .occ 1423, .occ 1462, .occ 1513, .occ 1522, .occ 1602, .occ 1606, .occ 1628, .occ 1654, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 17 (0), .branchGe 35 (1), .branchLe 25 (0), .branchLe 18 (0), .branchGe 42 (1), .branchLe 23 (0), .branchGe 14 (1)]

def plane484GenLeaf0029Mult : Fin 41 → Nat := ![101, 91, 185, 47, 62, 146, 62, 86, 184, 56, 158, 14, 40, 6, 44, 16, 98, 4, 6, 76, 60, 22, 138, 8, 8, 200, 4, 10, 42, 368, 318, 68, 368, 178, 282, 560, 328, 242, 550, 248, 1360]

theorem plane484GenLeaf0029 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0029Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0029Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0029Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0029Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 125
  · exact hroot.hOcc 128
  · exact hroot.hOcc 143
  · exact hroot.hOcc 179
  · exact hroot.hOcc 253
  · exact hroot.hOcc 284
  · exact hroot.hOcc 543
  · exact hroot.hOcc 558
  · exact hroot.hOcc 749
  · exact hroot.hOcc 787
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1368
  · exact hroot.hOcc 1369
  · exact hroot.hOcc 1388
  · exact hroot.hOcc 1392
  · exact hroot.hOcc 1400
  · exact hroot.hOcc 1412
  · exact hroot.hOcc 1422
  · exact hroot.hOcc 1423
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1513
  · exact hroot.hOcc 1522
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1628
  · exact hroot.hOcc 1654
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14

end QiushiMatmul
