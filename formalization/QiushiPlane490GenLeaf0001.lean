import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0001Refs : Fin 44 → RowRef 713 43 := ![.occ 86, .occ 93, .occ 100, .occ 103, .occ 104, .occ 109, .occ 114, .occ 124, .occ 133, .occ 141, .occ 147, .occ 154, .occ 198, .occ 199, .occ 236, .occ 283, .occ 332, .occ 336, .occ 354, .occ 362, .occ 368, .occ 447, .occ 466, .occ 489, .occ 503, .occ 521, .occ 533, .occ 589, .occ 653, .occ 667, .occ 678, .occ 692, .occ 703, .occ 710, .sumGe, .branchLe 29 (0), .branchLe 4 (0), .branchLe 23 (0), .branchLe 16 (0), .branchLe 39 (0), .branchLe 19 (0), .branchLe 10 (0), .branchLe 30 (0), .branchGe 12 (1)]

def plane490GenLeaf0001Mult : Fin 44 → Nat := ![2471, 1237, 2213, 2512, 3727, 762, 161, 906, 65, 3, 323, 1474, 1496, 2459, 94, 1880, 217, 483, 2448, 1329, 615, 1047, 95, 371, 425, 411, 1604, 1781, 296, 51, 792, 20, 785, 371, 5228, 4521, 5133, 4745, 4426, 5228, 5134, 1247, 4003, 12205]

theorem plane490GenLeaf0001 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0001Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0001Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 86
  · exact hroot.hOcc 93
  · exact hroot.hOcc 100
  · exact hroot.hOcc 103
  · exact hroot.hOcc 104
  · exact hroot.hOcc 109
  · exact hroot.hOcc 114
  · exact hroot.hOcc 124
  · exact hroot.hOcc 133
  · exact hroot.hOcc 141
  · exact hroot.hOcc 147
  · exact hroot.hOcc 154
  · exact hroot.hOcc 198
  · exact hroot.hOcc 199
  · exact hroot.hOcc 236
  · exact hroot.hOcc 283
  · exact hroot.hOcc 332
  · exact hroot.hOcc 336
  · exact hroot.hOcc 354
  · exact hroot.hOcc 362
  · exact hroot.hOcc 368
  · exact hroot.hOcc 447
  · exact hroot.hOcc 466
  · exact hroot.hOcc 489
  · exact hroot.hOcc 503
  · exact hroot.hOcc 521
  · exact hroot.hOcc 533
  · exact hroot.hOcc 589
  · exact hroot.hOcc 653
  · exact hroot.hOcc 667
  · exact hroot.hOcc 678
  · exact hroot.hOcc 692
  · exact hroot.hOcc 703
  · exact hroot.hOcc 710
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (12 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12

end QiushiMatmul
