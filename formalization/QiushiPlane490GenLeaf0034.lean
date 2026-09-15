import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0034Refs : Fin 44 → RowRef 713 43 := ![.occ 89, .occ 90, .occ 100, .occ 110, .occ 113, .occ 131, .occ 137, .occ 146, .occ 163, .occ 200, .occ 210, .occ 270, .occ 281, .occ 292, .occ 297, .occ 314, .occ 326, .occ 346, .occ 362, .occ 366, .occ 379, .occ 441, .occ 445, .occ 453, .occ 484, .occ 499, .occ 501, .occ 542, .occ 575, .occ 599, .occ 679, .occ 710, .sumGe, .branchLe 29 (0), .branchLe 4 (0), .branchGe 23 (1), .branchLe 30 (0), .branchLe 28 (0), .branchLe 35 (0), .branchLe 5 (0), .branchLe 38 (0), .branchLe 25 (0), .branchGe 15 (1), .branchGe 3 (1)]

def plane490GenLeaf0034Mult : Fin 44 → Nat := ![1208, 1274, 418, 528, 174, 1212, 804, 40, 352, 126, 88, 370, 149, 122, 109, 96, 838, 114, 128, 370, 964, 154, 220, 28, 88, 66, 62, 346, 291, 188, 51, 558, 1274, 1212, 840, 2578, 32, 926, 1274, 1274, 1274, 1274, 1960, 5332]

theorem plane490GenLeaf0034 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0034Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0034Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0034Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0034Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 89
  · exact hroot.hOcc 90
  · exact hroot.hOcc 100
  · exact hroot.hOcc 110
  · exact hroot.hOcc 113
  · exact hroot.hOcc 131
  · exact hroot.hOcc 137
  · exact hroot.hOcc 146
  · exact hroot.hOcc 163
  · exact hroot.hOcc 200
  · exact hroot.hOcc 210
  · exact hroot.hOcc 270
  · exact hroot.hOcc 281
  · exact hroot.hOcc 292
  · exact hroot.hOcc 297
  · exact hroot.hOcc 314
  · exact hroot.hOcc 326
  · exact hroot.hOcc 346
  · exact hroot.hOcc 362
  · exact hroot.hOcc 366
  · exact hroot.hOcc 379
  · exact hroot.hOcc 441
  · exact hroot.hOcc 445
  · exact hroot.hOcc 453
  · exact hroot.hOcc 484
  · exact hroot.hOcc 499
  · exact hroot.hOcc 501
  · exact hroot.hOcc 542
  · exact hroot.hOcc 575
  · exact hroot.hOcc 599
  · exact hroot.hOcc 679
  · exact hroot.hOcc 710
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (38 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3

end QiushiMatmul
