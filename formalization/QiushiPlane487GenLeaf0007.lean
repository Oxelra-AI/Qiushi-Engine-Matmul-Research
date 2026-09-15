import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0007Refs : Fin 49 → RowRef 668 48 := ![.occ 102, .occ 104, .occ 106, .occ 125, .occ 131, .occ 152, .occ 153, .occ 216, .occ 220, .occ 222, .occ 231, .occ 240, .occ 257, .occ 269, .occ 271, .occ 275, .occ 283, .occ 303, .occ 315, .occ 317, .occ 347, .occ 352, .occ 379, .occ 380, .occ 386, .occ 387, .occ 388, .occ 390, .occ 399, .occ 546, .occ 577, .occ 586, .occ 587, .occ 608, .occ 611, .occ 639, .occ 648, .occ 653, .sumGe, .nonneg 3, .nonneg 8, .branchLe 39 (0), .branchLe 23 (0), .branchLe 6 (0), .branchLe 25 (0), .branchLe 12 (0), .branchLe 15 (0), .branchGe 16 (1), .branchGe 14 (1)]

def plane487GenLeaf0007Mult : Fin 49 → Nat := ![11681, 8421, 2031, 23179, 4617, 8028, 5737, 19228, 1351, 10807, 4504, 535, 13999, 11135, 1019, 4555, 2973, 18019, 2094, 1832, 9021, 6237, 566, 5003, 2515, 5256, 13123, 3249, 11043, 9547, 5157, 1404, 1392, 4163, 4716, 14016, 4009, 6965, 43705, 3538, 557, 27193, 27693, 39696, 28653, 20964, 11970, 90975, 72397]

theorem plane487GenLeaf0007 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0007Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0007Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0007Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0007Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 102
  · exact hroot.hOcc 104
  · exact hroot.hOcc 106
  · exact hroot.hOcc 125
  · exact hroot.hOcc 131
  · exact hroot.hOcc 152
  · exact hroot.hOcc 153
  · exact hroot.hOcc 216
  · exact hroot.hOcc 220
  · exact hroot.hOcc 222
  · exact hroot.hOcc 231
  · exact hroot.hOcc 240
  · exact hroot.hOcc 257
  · exact hroot.hOcc 269
  · exact hroot.hOcc 271
  · exact hroot.hOcc 275
  · exact hroot.hOcc 283
  · exact hroot.hOcc 303
  · exact hroot.hOcc 315
  · exact hroot.hOcc 317
  · exact hroot.hOcc 347
  · exact hroot.hOcc 352
  · exact hroot.hOcc 379
  · exact hroot.hOcc 380
  · exact hroot.hOcc 386
  · exact hroot.hOcc 387
  · exact hroot.hOcc 388
  · exact hroot.hOcc 390
  · exact hroot.hOcc 399
  · exact hroot.hOcc 546
  · exact hroot.hOcc 577
  · exact hroot.hOcc 586
  · exact hroot.hOcc 587
  · exact hroot.hOcc 608
  · exact hroot.hOcc 611
  · exact hroot.hOcc 639
  · exact hroot.hOcc 648
  · exact hroot.hOcc 653
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (8 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (6 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (25 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (12 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (15 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (16 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (14 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14

end QiushiMatmul
