import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0047Refs : Fin 44 → RowRef 713 43 := ![.occ 86, .occ 89, .occ 91, .occ 94, .occ 95, .occ 103, .occ 116, .occ 147, .occ 149, .occ 154, .occ 164, .occ 201, .occ 236, .occ 238, .occ 239, .occ 263, .occ 274, .occ 280, .occ 284, .occ 312, .occ 335, .occ 362, .occ 447, .occ 480, .occ 489, .occ 525, .occ 534, .occ 537, .occ 627, .occ 637, .occ 640, .occ 673, .occ 689, .occ 703, .sumGe, .branchLe 29 (0), .branchLe 4 (0), .branchGe 23 (1), .branchLe 30 (0), .branchGe 28 (1), .branchLe 39 (0), .branchLe 21 (0), .branchLe 33 (0), .branchLe 14 (0)]

def plane490GenLeaf0047Mult : Fin 44 → Nat := ![838, 745, 810, 871, 20, 91, 1209, 654, 329, 758, 7, 97, 413, 135, 128, 1032, 239, 124, 343, 374, 520, 745, 147, 640, 48, 191, 21, 419, 166, 598, 202, 156, 183, 420, 1954, 1731, 1559, 374, 1906, 6587, 1954, 509, 1222, 1857]

theorem plane490GenLeaf0047 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0047Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0047Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0047Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0047Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 86
  · exact hroot.hOcc 89
  · exact hroot.hOcc 91
  · exact hroot.hOcc 94
  · exact hroot.hOcc 95
  · exact hroot.hOcc 103
  · exact hroot.hOcc 116
  · exact hroot.hOcc 147
  · exact hroot.hOcc 149
  · exact hroot.hOcc 154
  · exact hroot.hOcc 164
  · exact hroot.hOcc 201
  · exact hroot.hOcc 236
  · exact hroot.hOcc 238
  · exact hroot.hOcc 239
  · exact hroot.hOcc 263
  · exact hroot.hOcc 274
  · exact hroot.hOcc 280
  · exact hroot.hOcc 284
  · exact hroot.hOcc 312
  · exact hroot.hOcc 335
  · exact hroot.hOcc 362
  · exact hroot.hOcc 447
  · exact hroot.hOcc 480
  · exact hroot.hOcc 489
  · exact hroot.hOcc 525
  · exact hroot.hOcc 534
  · exact hroot.hOcc 537
  · exact hroot.hOcc 627
  · exact hroot.hOcc 637
  · exact hroot.hOcc 640
  · exact hroot.hOcc 673
  · exact hroot.hOcc 689
  · exact hroot.hOcc 703
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (21 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (33 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14

end QiushiMatmul
