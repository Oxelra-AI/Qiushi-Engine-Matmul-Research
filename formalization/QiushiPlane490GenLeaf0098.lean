import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0098Refs : Fin 44 → RowRef 713 43 := ![.occ 89, .occ 90, .occ 105, .occ 108, .occ 109, .occ 112, .occ 155, .occ 159, .occ 160, .occ 163, .occ 177, .occ 188, .occ 266, .occ 279, .occ 283, .occ 299, .occ 304, .occ 312, .occ 323, .occ 336, .occ 378, .occ 479, .occ 486, .occ 521, .occ 540, .occ 542, .occ 582, .occ 590, .occ 593, .occ 602, .occ 632, .occ 636, .occ 671, .occ 679, .occ 683, .occ 706, .occ 710, .sumGe, .branchGe 29 (1), .branchGe 18 (1), .branchLe 14 (0), .branchLe 1 (0), .branchLe 21 (0), .branchGe 3 (1)]

def plane490GenLeaf0098Mult : Fin 44 → Nat := ![1538, 1966, 1457, 1719, 576, 139, 161, 1008, 365, 813, 65, 146, 186, 330, 87, 519, 346, 70, 161, 61, 115, 123, 370, 50, 385, 4, 537, 192, 510, 846, 428, 51, 519, 247, 401, 108, 121, 1966, 6797, 2096, 1395, 1966, 1444, 5821]

theorem plane490GenLeaf0098 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0098Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0098Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0098Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0098Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 89
  · exact hroot.hOcc 90
  · exact hroot.hOcc 105
  · exact hroot.hOcc 108
  · exact hroot.hOcc 109
  · exact hroot.hOcc 112
  · exact hroot.hOcc 155
  · exact hroot.hOcc 159
  · exact hroot.hOcc 160
  · exact hroot.hOcc 163
  · exact hroot.hOcc 177
  · exact hroot.hOcc 188
  · exact hroot.hOcc 266
  · exact hroot.hOcc 279
  · exact hroot.hOcc 283
  · exact hroot.hOcc 299
  · exact hroot.hOcc 304
  · exact hroot.hOcc 312
  · exact hroot.hOcc 323
  · exact hroot.hOcc 336
  · exact hroot.hOcc 378
  · exact hroot.hOcc 479
  · exact hroot.hOcc 486
  · exact hroot.hOcc 521
  · exact hroot.hOcc 540
  · exact hroot.hOcc 542
  · exact hroot.hOcc 582
  · exact hroot.hOcc 590
  · exact hroot.hOcc 593
  · exact hroot.hOcc 602
  · exact hroot.hOcc 632
  · exact hroot.hOcc 636
  · exact hroot.hOcc 671
  · exact hroot.hOcc 679
  · exact hroot.hOcc 683
  · exact hroot.hOcc 706
  · exact hroot.hOcc 710
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (21 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3

end QiushiMatmul
