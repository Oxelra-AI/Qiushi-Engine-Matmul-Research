import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0048Refs : Fin 44 → RowRef 713 43 := ![.occ 91, .occ 99, .occ 107, .occ 133, .occ 139, .occ 140, .occ 154, .occ 164, .occ 201, .occ 203, .occ 205, .occ 238, .occ 239, .occ 245, .occ 280, .occ 284, .occ 315, .occ 335, .occ 362, .occ 364, .occ 449, .occ 480, .occ 493, .occ 499, .occ 549, .occ 601, .occ 627, .occ 637, .occ 655, .occ 676, .occ 679, .occ 692, .occ 711, .sumGe, .nonneg 26, .branchLe 29 (0), .branchLe 4 (0), .branchGe 23 (1), .branchLe 30 (0), .branchGe 28 (1), .branchLe 39 (0), .branchLe 21 (0), .branchLe 33 (0), .branchGe 14 (1)]

def plane490GenLeaf0048Mult : Fin 44 → Nat := ![110, 2, 94, 245, 35, 13, 89, 61, 208, 109, 112, 70, 275, 12, 24, 32, 419, 202, 5, 358, 48, 119, 20, 58, 24, 50, 96, 79, 20, 114, 50, 34, 150, 529, 76, 509, 509, 724, 171, 999, 379, 479, 293, 1343]

theorem plane490GenLeaf0048 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0048Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0048Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0048Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0048Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 91
  · exact hroot.hOcc 99
  · exact hroot.hOcc 107
  · exact hroot.hOcc 133
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 154
  · exact hroot.hOcc 164
  · exact hroot.hOcc 201
  · exact hroot.hOcc 203
  · exact hroot.hOcc 205
  · exact hroot.hOcc 238
  · exact hroot.hOcc 239
  · exact hroot.hOcc 245
  · exact hroot.hOcc 280
  · exact hroot.hOcc 284
  · exact hroot.hOcc 315
  · exact hroot.hOcc 335
  · exact hroot.hOcc 362
  · exact hroot.hOcc 364
  · exact hroot.hOcc 449
  · exact hroot.hOcc 480
  · exact hroot.hOcc 493
  · exact hroot.hOcc 499
  · exact hroot.hOcc 549
  · exact hroot.hOcc 601
  · exact hroot.hOcc 627
  · exact hroot.hOcc 637
  · exact hroot.hOcc 655
  · exact hroot.hOcc 676
  · exact hroot.hOcc 679
  · exact hroot.hOcc 692
  · exact hroot.hOcc 711
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (21 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (33 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14

end QiushiMatmul
