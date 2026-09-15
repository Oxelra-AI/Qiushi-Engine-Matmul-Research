import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0067Refs : Fin 49 → RowRef 668 48 := ![.occ 83, .occ 85, .occ 94, .occ 95, .occ 101, .occ 106, .occ 145, .occ 146, .occ 170, .occ 184, .occ 190, .occ 223, .occ 241, .occ 246, .occ 253, .occ 259, .occ 294, .occ 299, .occ 303, .occ 333, .occ 351, .occ 353, .occ 370, .occ 390, .occ 391, .occ 470, .occ 491, .occ 527, .occ 539, .occ 543, .occ 544, .occ 594, .occ 628, .occ 639, .occ 650, .occ 653, .occ 657, .sumGe, .nonneg 7, .nonneg 8, .branchGe 39 (1), .branchLe 28 (0), .branchLe 40 (0), .branchGe 29 (1), .branchLe 10 (0), .branchLe 12 (0), .branchLe 16 (0), .branchLe 20 (0), .branchLe 11 (0)]

def plane487GenLeaf0067Mult : Fin 49 → Nat := ![21383, 29489, 5914, 8099, 104955, 17339, 21303, 29213, 4507, 26251, 112205, 15001, 40897, 46617, 25613, 122, 1854, 33365, 8681, 54437, 20106, 43740, 4658, 31388, 14040, 5885, 9568, 10327, 8093, 6896, 13104, 26461, 7064, 3789, 15913, 3461, 19753, 112205, 37019, 32881, 115010, 99101, 100063, 381075, 88991, 86618, 100323, 92452, 55395]

theorem plane487GenLeaf0067 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0067Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0067Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0067Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0067Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 83
  · exact hroot.hOcc 85
  · exact hroot.hOcc 94
  · exact hroot.hOcc 95
  · exact hroot.hOcc 101
  · exact hroot.hOcc 106
  · exact hroot.hOcc 145
  · exact hroot.hOcc 146
  · exact hroot.hOcc 170
  · exact hroot.hOcc 184
  · exact hroot.hOcc 190
  · exact hroot.hOcc 223
  · exact hroot.hOcc 241
  · exact hroot.hOcc 246
  · exact hroot.hOcc 253
  · exact hroot.hOcc 259
  · exact hroot.hOcc 294
  · exact hroot.hOcc 299
  · exact hroot.hOcc 303
  · exact hroot.hOcc 333
  · exact hroot.hOcc 351
  · exact hroot.hOcc 353
  · exact hroot.hOcc 370
  · exact hroot.hOcc 390
  · exact hroot.hOcc 391
  · exact hroot.hOcc 470
  · exact hroot.hOcc 491
  · exact hroot.hOcc 527
  · exact hroot.hOcc 539
  · exact hroot.hOcc 543
  · exact hroot.hOcc 544
  · exact hroot.hOcc 594
  · exact hroot.hOcc 628
  · exact hroot.hOcc 639
  · exact hroot.hOcc 650
  · exact hroot.hOcc 653
  · exact hroot.hOcc 657
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (8 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (39 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (28 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (40 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (29 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (10 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (12 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (16 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (20 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (11 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11

end QiushiMatmul
