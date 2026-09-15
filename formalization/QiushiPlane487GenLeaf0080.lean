import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0080Refs : Fin 48 → RowRef 668 48 := ![.occ 83, .occ 87, .occ 94, .occ 100, .occ 105, .occ 147, .occ 161, .occ 174, .occ 177, .occ 196, .occ 200, .occ 217, .occ 237, .occ 238, .occ 239, .occ 264, .occ 281, .occ 284, .occ 301, .occ 315, .occ 316, .occ 323, .occ 336, .occ 347, .occ 352, .occ 377, .occ 389, .occ 401, .occ 544, .occ 546, .occ 575, .occ 598, .occ 655, .occ 656, .occ 660, .occ 661, .occ 665, .sumGe, .nonneg 8, .nonneg 30, .branchGe 39 (1), .branchGe 28 (1), .branchLe 3 (0), .branchLe 36 (0), .branchLe 35 (0), .branchLe 13 (0), .branchGe 37 (1), .branchGe 9 (1)]

def plane487GenLeaf0080Mult : Fin 48 → Nat := ![172, 8, 6, 30, 186, 196, 58, 27, 66, 102, 29, 30, 72, 65, 51, 293, 16, 85, 29, 66, 13, 14, 30, 22, 36, 52, 32, 131, 108, 44, 22, 42, 44, 14, 102, 67, 95, 335, 60, 25, 786, 990, 335, 255, 279, 108, 446, 473]

theorem plane487GenLeaf0080 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    (hUB_36 : x 36 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0080Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0080Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0080Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0080Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 83
  · exact hroot.hOcc 87
  · exact hroot.hOcc 94
  · exact hroot.hOcc 100
  · exact hroot.hOcc 105
  · exact hroot.hOcc 147
  · exact hroot.hOcc 161
  · exact hroot.hOcc 174
  · exact hroot.hOcc 177
  · exact hroot.hOcc 196
  · exact hroot.hOcc 200
  · exact hroot.hOcc 217
  · exact hroot.hOcc 237
  · exact hroot.hOcc 238
  · exact hroot.hOcc 239
  · exact hroot.hOcc 264
  · exact hroot.hOcc 281
  · exact hroot.hOcc 284
  · exact hroot.hOcc 301
  · exact hroot.hOcc 315
  · exact hroot.hOcc 316
  · exact hroot.hOcc 323
  · exact hroot.hOcc 336
  · exact hroot.hOcc 347
  · exact hroot.hOcc 352
  · exact hroot.hOcc 377
  · exact hroot.hOcc 389
  · exact hroot.hOcc 401
  · exact hroot.hOcc 544
  · exact hroot.hOcc 546
  · exact hroot.hOcc 575
  · exact hroot.hOcc 598
  · exact hroot.hOcc 655
  · exact hroot.hOcc 656
  · exact hroot.hOcc 660
  · exact hroot.hOcc 661
  · exact hroot.hOcc 665
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (30 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (39 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (28 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (3 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (36 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (35 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (13 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (37 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37
  · change (∑ k, (if k = (9 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9

end QiushiMatmul
