import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0054Refs : Fin 49 → RowRef 668 48 := ![.occ 89, .occ 94, .occ 108, .occ 111, .occ 123, .occ 163, .occ 188, .occ 207, .occ 209, .occ 225, .occ 230, .occ 231, .occ 246, .occ 255, .occ 258, .occ 294, .occ 303, .occ 306, .occ 336, .occ 347, .occ 391, .occ 401, .occ 405, .occ 414, .occ 466, .occ 472, .occ 523, .occ 526, .occ 539, .occ 631, .occ 649, .occ 650, .occ 653, .occ 656, .occ 666, .sumGe, .nonneg 0, .nonneg 7, .branchGe 39 (1), .branchLe 28 (0), .branchLe 40 (0), .branchLe 29 (0), .branchLe 19 (0), .branchLe 36 (0), .branchLe 23 (0), .branchLe 45 (0), .branchGe 5 (1), .branchGe 1 (1), .branchGe 26 (1)]

def plane487GenLeaf0054Mult : Fin 49 → Nat := ![1303, 18079, 9467, 8706, 967, 3613, 2703, 4986, 487, 939, 8316, 5733, 7705, 6374, 1233, 6075, 2508, 6011, 1448, 6983, 10840, 7927, 806, 5016, 130, 2326, 1671, 4704, 2364, 115, 3810, 806, 2567, 4778, 1251, 21838, 650, 6093, 7235, 16777, 14437, 18028, 17823, 10149, 10952, 2830, 35660, 25560, 59331]

theorem plane487GenLeaf0054 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_45 : x 45 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0054Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0054Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0054Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0054Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 89
  · exact hroot.hOcc 94
  · exact hroot.hOcc 108
  · exact hroot.hOcc 111
  · exact hroot.hOcc 123
  · exact hroot.hOcc 163
  · exact hroot.hOcc 188
  · exact hroot.hOcc 207
  · exact hroot.hOcc 209
  · exact hroot.hOcc 225
  · exact hroot.hOcc 230
  · exact hroot.hOcc 231
  · exact hroot.hOcc 246
  · exact hroot.hOcc 255
  · exact hroot.hOcc 258
  · exact hroot.hOcc 294
  · exact hroot.hOcc 303
  · exact hroot.hOcc 306
  · exact hroot.hOcc 336
  · exact hroot.hOcc 347
  · exact hroot.hOcc 391
  · exact hroot.hOcc 401
  · exact hroot.hOcc 405
  · exact hroot.hOcc 414
  · exact hroot.hOcc 466
  · exact hroot.hOcc 472
  · exact hroot.hOcc 523
  · exact hroot.hOcc 526
  · exact hroot.hOcc 539
  · exact hroot.hOcc 631
  · exact hroot.hOcc 649
  · exact hroot.hOcc 650
  · exact hroot.hOcc 653
  · exact hroot.hOcc 656
  · exact hroot.hOcc 666
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (7 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (39 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (28 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (40 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (29 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (19 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (36 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (45 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_45
  · change (∑ k, (if k = (5 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5
  · change (∑ k, (if k = (1 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (26 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26

end QiushiMatmul
