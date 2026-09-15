import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0080Refs : Fin 50 → RowRef 726 49 := ![.occ 80, .occ 87, .occ 98, .occ 101, .occ 110, .occ 118, .occ 123, .occ 141, .occ 213, .occ 219, .occ 231, .occ 234, .occ 240, .occ 243, .occ 281, .occ 305, .occ 320, .occ 329, .occ 332, .occ 346, .occ 359, .occ 387, .occ 393, .occ 401, .occ 410, .occ 423, .occ 425, .occ 484, .occ 493, .occ 504, .occ 540, .occ 552, .occ 610, .occ 652, .occ 662, .occ 671, .occ 685, .occ 687, .occ 711, .sumGe, .nonneg 7, .nonneg 46, .branchGe 31 (1), .branchLe 44 (0), .branchLe 11 (0), .branchLe 27 (0), .branchGe 22 (1), .branchLe 3 (0), .branchLe 23 (0), .branchGe 8 (1)]

def plane491GenLeaf0080Mult : Fin 50 → Nat := ![19013, 33486, 7789, 4402, 9170, 882, 59505, 23297, 14630, 12411, 1096, 9498, 19969, 9982, 579, 2101, 14849, 25744, 27444, 3021, 16159, 8255, 24003, 3717, 11944, 14505, 22449, 32003, 9925, 1453, 8624, 9630, 24306, 22951, 17330, 13642, 17511, 10114, 4850, 85091, 23061, 24526, 126024, 60039, 44810, 85091, 159455, 41710, 65146, 157323]

theorem plane491GenLeaf0080 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0080Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0080Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0080Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0080Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 80
  · exact hroot.hOcc 87
  · exact hroot.hOcc 98
  · exact hroot.hOcc 101
  · exact hroot.hOcc 110
  · exact hroot.hOcc 118
  · exact hroot.hOcc 123
  · exact hroot.hOcc 141
  · exact hroot.hOcc 213
  · exact hroot.hOcc 219
  · exact hroot.hOcc 231
  · exact hroot.hOcc 234
  · exact hroot.hOcc 240
  · exact hroot.hOcc 243
  · exact hroot.hOcc 281
  · exact hroot.hOcc 305
  · exact hroot.hOcc 320
  · exact hroot.hOcc 329
  · exact hroot.hOcc 332
  · exact hroot.hOcc 346
  · exact hroot.hOcc 359
  · exact hroot.hOcc 387
  · exact hroot.hOcc 393
  · exact hroot.hOcc 401
  · exact hroot.hOcc 410
  · exact hroot.hOcc 423
  · exact hroot.hOcc 425
  · exact hroot.hOcc 484
  · exact hroot.hOcc 493
  · exact hroot.hOcc 504
  · exact hroot.hOcc 540
  · exact hroot.hOcc 552
  · exact hroot.hOcc 610
  · exact hroot.hOcc 652
  · exact hroot.hOcc 662
  · exact hroot.hOcc 671
  · exact hroot.hOcc 685
  · exact hroot.hOcc 687
  · exact hroot.hOcc 711
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (46 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (11 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (22 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22
  · change (∑ k, (if k = (3 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (23 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (8 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8

end QiushiMatmul
