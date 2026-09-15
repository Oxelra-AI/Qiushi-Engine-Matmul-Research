import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0083Refs : Fin 49 → RowRef 668 48 := ![.occ 85, .occ 94, .occ 95, .occ 128, .occ 130, .occ 147, .occ 155, .occ 161, .occ 163, .occ 180, .occ 190, .occ 196, .occ 198, .occ 237, .occ 239, .occ 240, .occ 244, .occ 284, .occ 288, .occ 308, .occ 332, .occ 344, .occ 377, .occ 378, .occ 380, .occ 386, .occ 401, .occ 443, .occ 451, .occ 521, .occ 523, .occ 547, .occ 548, .occ 598, .occ 604, .occ 608, .occ 651, .occ 661, .occ 665, .sumGe, .nonneg 40, .nonneg 47, .branchGe 39 (1), .branchLe 7 (0), .branchGe 28 (1), .branchLe 3 (0), .branchLe 36 (0), .branchGe 35 (1), .branchGe 19 (1)]

def plane487GenLeaf0083Mult : Fin 49 → Nat := ![55, 86, 47, 121, 216, 129, 9, 194, 82, 14, 4, 32, 86, 32, 17, 96, 28, 9, 197, 65, 110, 29, 49, 78, 61, 129, 47, 27, 48, 11, 3, 42, 28, 54, 24, 4, 40, 38, 89, 286, 146, 33, 448, 178, 674, 262, 168, 625, 873]

theorem plane487GenLeaf0083 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_36 : x 36 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0083Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0083Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0083Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0083Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 85
  · exact hroot.hOcc 94
  · exact hroot.hOcc 95
  · exact hroot.hOcc 128
  · exact hroot.hOcc 130
  · exact hroot.hOcc 147
  · exact hroot.hOcc 155
  · exact hroot.hOcc 161
  · exact hroot.hOcc 163
  · exact hroot.hOcc 180
  · exact hroot.hOcc 190
  · exact hroot.hOcc 196
  · exact hroot.hOcc 198
  · exact hroot.hOcc 237
  · exact hroot.hOcc 239
  · exact hroot.hOcc 240
  · exact hroot.hOcc 244
  · exact hroot.hOcc 284
  · exact hroot.hOcc 288
  · exact hroot.hOcc 308
  · exact hroot.hOcc 332
  · exact hroot.hOcc 344
  · exact hroot.hOcc 377
  · exact hroot.hOcc 378
  · exact hroot.hOcc 380
  · exact hroot.hOcc 386
  · exact hroot.hOcc 401
  · exact hroot.hOcc 443
  · exact hroot.hOcc 451
  · exact hroot.hOcc 521
  · exact hroot.hOcc 523
  · exact hroot.hOcc 547
  · exact hroot.hOcc 548
  · exact hroot.hOcc 598
  · exact hroot.hOcc 604
  · exact hroot.hOcc 608
  · exact hroot.hOcc 651
  · exact hroot.hOcc 661
  · exact hroot.hOcc 665
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (40 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (47 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (39 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (7 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (28 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (3 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (36 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (35 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (19 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19

end QiushiMatmul
