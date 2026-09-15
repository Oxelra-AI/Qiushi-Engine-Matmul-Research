import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0075Refs : Fin 49 → RowRef 668 48 := ![.occ 80, .occ 87, .occ 94, .occ 96, .occ 100, .occ 107, .occ 109, .occ 160, .occ 168, .occ 181, .occ 214, .occ 219, .occ 246, .occ 256, .occ 260, .occ 261, .occ 275, .occ 288, .occ 297, .occ 303, .occ 305, .occ 313, .occ 315, .occ 332, .occ 378, .occ 381, .occ 386, .occ 390, .occ 394, .occ 399, .occ 472, .occ 482, .occ 484, .occ 493, .occ 505, .occ 509, .occ 563, .occ 619, .occ 623, .occ 653, .occ 664, .sumGe, .nonneg 7, .nonneg 22, .branchGe 39 (1), .branchLe 28 (0), .branchGe 40 (1), .branchLe 13 (0), .branchGe 32 (1)]

def plane487GenLeaf0075Mult : Fin 49 → Nat := ![3049, 286, 10895, 3257, 159, 3337, 2297, 928, 2583, 3137, 2773, 541, 1359, 2064, 1379, 2182, 3542, 4313, 4575, 2486, 8211, 5932, 3180, 4387, 3908, 321, 4551, 286, 891, 1801, 1326, 1688, 1359, 907, 3954, 1720, 8093, 732, 2054, 1560, 4577, 16915, 2898, 2557, 23822, 7086, 51087, 15355, 26947]

theorem plane487GenLeaf0075 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_40 : (1 : Int) ≤ x 40)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0075Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0075Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0075Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0075Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 80
  · exact hroot.hOcc 87
  · exact hroot.hOcc 94
  · exact hroot.hOcc 96
  · exact hroot.hOcc 100
  · exact hroot.hOcc 107
  · exact hroot.hOcc 109
  · exact hroot.hOcc 160
  · exact hroot.hOcc 168
  · exact hroot.hOcc 181
  · exact hroot.hOcc 214
  · exact hroot.hOcc 219
  · exact hroot.hOcc 246
  · exact hroot.hOcc 256
  · exact hroot.hOcc 260
  · exact hroot.hOcc 261
  · exact hroot.hOcc 275
  · exact hroot.hOcc 288
  · exact hroot.hOcc 297
  · exact hroot.hOcc 303
  · exact hroot.hOcc 305
  · exact hroot.hOcc 313
  · exact hroot.hOcc 315
  · exact hroot.hOcc 332
  · exact hroot.hOcc 378
  · exact hroot.hOcc 381
  · exact hroot.hOcc 386
  · exact hroot.hOcc 390
  · exact hroot.hOcc 394
  · exact hroot.hOcc 399
  · exact hroot.hOcc 472
  · exact hroot.hOcc 482
  · exact hroot.hOcc 484
  · exact hroot.hOcc 493
  · exact hroot.hOcc 505
  · exact hroot.hOcc 509
  · exact hroot.hOcc 563
  · exact hroot.hOcc 619
  · exact hroot.hOcc 623
  · exact hroot.hOcc 653
  · exact hroot.hOcc 664
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (22 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (39 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (28 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (40 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_40
  · change (∑ k, (if k = (13 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (32 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32

end QiushiMatmul
