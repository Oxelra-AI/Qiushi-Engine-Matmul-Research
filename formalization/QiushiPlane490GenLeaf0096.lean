import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0096Refs : Fin 44 → RowRef 713 43 := ![.occ 103, .occ 105, .occ 108, .occ 109, .occ 111, .occ 116, .occ 159, .occ 170, .occ 188, .occ 224, .occ 225, .occ 283, .occ 284, .occ 299, .occ 302, .occ 304, .occ 312, .occ 319, .occ 335, .occ 336, .occ 349, .occ 354, .occ 395, .occ 406, .occ 448, .occ 489, .occ 494, .occ 517, .occ 522, .occ 561, .occ 582, .occ 602, .occ 603, .occ 653, .occ 666, .sumGe, .nonneg 24, .branchGe 29 (1), .branchGe 18 (1), .branchLe 14 (0), .branchLe 1 (0), .branchLe 21 (0), .branchLe 3 (0), .branchLe 20 (0)]

def plane490GenLeaf0096Mult : Fin 44 → Nat := ![459, 2169, 2656, 1211, 644, 125, 90, 158, 958, 1286, 442, 376, 42, 885, 61, 132, 50, 601, 588, 350, 608, 411, 74, 182, 383, 224, 143, 68, 445, 301, 1937, 1569, 6, 27, 487, 2656, 1165, 8135, 6257, 2238, 2629, 2656, 2656, 2080]

theorem plane490GenLeaf0096 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0096Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0096Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0096Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0096Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 103
  · exact hroot.hOcc 105
  · exact hroot.hOcc 108
  · exact hroot.hOcc 109
  · exact hroot.hOcc 111
  · exact hroot.hOcc 116
  · exact hroot.hOcc 159
  · exact hroot.hOcc 170
  · exact hroot.hOcc 188
  · exact hroot.hOcc 224
  · exact hroot.hOcc 225
  · exact hroot.hOcc 283
  · exact hroot.hOcc 284
  · exact hroot.hOcc 299
  · exact hroot.hOcc 302
  · exact hroot.hOcc 304
  · exact hroot.hOcc 312
  · exact hroot.hOcc 319
  · exact hroot.hOcc 335
  · exact hroot.hOcc 336
  · exact hroot.hOcc 349
  · exact hroot.hOcc 354
  · exact hroot.hOcc 395
  · exact hroot.hOcc 406
  · exact hroot.hOcc 448
  · exact hroot.hOcc 489
  · exact hroot.hOcc 494
  · exact hroot.hOcc 517
  · exact hroot.hOcc 522
  · exact hroot.hOcc 561
  · exact hroot.hOcc 582
  · exact hroot.hOcc 602
  · exact hroot.hOcc 603
  · exact hroot.hOcc 653
  · exact hroot.hOcc 666
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (21 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20

end QiushiMatmul
