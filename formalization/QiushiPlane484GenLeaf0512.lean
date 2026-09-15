import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0512Refs : Fin 42 → RowRef 1665 43 := ![.occ 124, .occ 127, .occ 133, .occ 135, .occ 140, .occ 202, .occ 285, .occ 294, .occ 473, .occ 550, .occ 683, .occ 1234, .occ 1275, .occ 1279, .occ 1293, .occ 1298, .occ 1299, .occ 1343, .occ 1347, .occ 1447, .occ 1472, .occ 1481, .occ 1483, .occ 1514, .occ 1515, .occ 1539, .occ 1540, .occ 1546, .occ 1590, .occ 1632, .occ 1637, .sumGe, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchLe 26 (0), .branchLe 30 (0), .branchLe 34 (0), .branchLe 8 (0), .branchGe 33 (1), .branchLe 3 (0), .branchLe 0 (0)]

def plane484GenLeaf0512Mult : Fin 42 → Nat := ![1470, 864, 3589, 1102, 321, 4953, 1215, 609, 6553, 2334, 584, 91, 1408, 3536, 244, 372, 1515, 77, 1510, 62, 379, 3343, 3550, 1821, 1076, 1744, 1032, 31, 2476, 2131, 295, 9760, 10286, 27907, 2632, 7013, 9683, 8050, 9465, 27465, 9290, 9760]

theorem plane484GenLeaf0512 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_33 : (1 : Int) ≤ x 33)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0512Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0512Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0512Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0512Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 124
  · exact hroot.hOcc 127
  · exact hroot.hOcc 133
  · exact hroot.hOcc 135
  · exact hroot.hOcc 140
  · exact hroot.hOcc 202
  · exact hroot.hOcc 285
  · exact hroot.hOcc 294
  · exact hroot.hOcc 473
  · exact hroot.hOcc 550
  · exact hroot.hOcc 683
  · exact hroot.hOcc 1234
  · exact hroot.hOcc 1275
  · exact hroot.hOcc 1279
  · exact hroot.hOcc 1293
  · exact hroot.hOcc 1298
  · exact hroot.hOcc 1299
  · exact hroot.hOcc 1343
  · exact hroot.hOcc 1347
  · exact hroot.hOcc 1447
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1514
  · exact hroot.hOcc 1515
  · exact hroot.hOcc 1539
  · exact hroot.hOcc 1540
  · exact hroot.hOcc 1546
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1632
  · exact hroot.hOcc 1637
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (33 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_33
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0

end QiushiMatmul
