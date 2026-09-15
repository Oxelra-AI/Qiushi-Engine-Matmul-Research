import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0432Refs : Fin 41 → RowRef 1665 43 := ![.occ 105, .occ 125, .occ 130, .occ 140, .occ 283, .occ 297, .occ 355, .occ 397, .occ 398, .occ 578, .occ 691, .occ 858, .occ 1158, .occ 1174, .occ 1190, .occ 1200, .occ 1225, .occ 1249, .occ 1298, .occ 1350, .occ 1385, .occ 1432, .occ 1454, .occ 1470, .occ 1475, .occ 1483, .occ 1544, .occ 1615, .occ 1630, .occ 1654, .sumGe, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 0 (0), .branchLe 29 (0), .branchLe 23 (0), .branchLe 19 (0), .branchGe 40 (1), .branchLe 6 (0), .branchLe 41 (0)]

def plane484GenLeaf0432Mult : Fin 41 → Nat := ![1258, 274, 2887, 3787, 770, 1606, 929, 1450, 711, 115, 181, 2330, 1264, 274, 1017, 1805, 253, 659, 610, 3523, 112, 1885, 720, 1017, 989, 2061, 1165, 148, 555, 95, 7487, 14655, 4067, 7118, 3188, 7487, 7487, 7487, 8611, 6128, 5811]

theorem plane484GenLeaf0432 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_40 : (1 : Int) ≤ x 40)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_41 : x 41 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0432Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0432Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0432Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0432Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 105
  · exact hroot.hOcc 125
  · exact hroot.hOcc 130
  · exact hroot.hOcc 140
  · exact hroot.hOcc 283
  · exact hroot.hOcc 297
  · exact hroot.hOcc 355
  · exact hroot.hOcc 397
  · exact hroot.hOcc 398
  · exact hroot.hOcc 578
  · exact hroot.hOcc 691
  · exact hroot.hOcc 858
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1225
  · exact hroot.hOcc 1249
  · exact hroot.hOcc 1298
  · exact hroot.hOcc 1350
  · exact hroot.hOcc 1385
  · exact hroot.hOcc 1432
  · exact hroot.hOcc 1454
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1475
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1544
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1630
  · exact hroot.hOcc 1654
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (40 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_40
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (41 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_41

end QiushiMatmul
