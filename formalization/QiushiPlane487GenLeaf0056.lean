import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0056Refs : Fin 49 → RowRef 668 48 := ![.occ 83, .occ 85, .occ 89, .occ 100, .occ 102, .occ 103, .occ 118, .occ 122, .occ 134, .occ 157, .occ 165, .occ 196, .occ 201, .occ 211, .occ 225, .occ 233, .occ 269, .occ 277, .occ 295, .occ 297, .occ 302, .occ 313, .occ 347, .occ 381, .occ 409, .occ 440, .occ 453, .occ 457, .occ 470, .occ 472, .occ 526, .occ 569, .occ 573, .occ 604, .occ 637, .occ 645, .occ 661, .occ 665, .sumGe, .branchGe 39 (1), .branchLe 7 (0), .branchLe 28 (0), .branchLe 40 (0), .branchLe 29 (0), .branchLe 19 (0), .branchLe 36 (0), .branchLe 23 (0), .branchGe 45 (1), .branchGe 10 (1)]

def plane487GenLeaf0056Mult : Fin 49 → Nat := ![345, 535, 145, 407, 948, 244, 999, 961, 239, 85, 941, 449, 675, 103, 74, 361, 205, 331, 663, 182, 261, 383, 14, 684, 901, 296, 238, 351, 8, 423, 565, 382, 28, 6, 126, 45, 21, 28, 1396, 3222, 278, 760, 562, 1141, 1368, 1388, 786, 3464, 5883]

theorem plane487GenLeaf0056 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_45 : (1 : Int) ≤ x 45)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0056Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0056Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0056Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0056Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 83
  · exact hroot.hOcc 85
  · exact hroot.hOcc 89
  · exact hroot.hOcc 100
  · exact hroot.hOcc 102
  · exact hroot.hOcc 103
  · exact hroot.hOcc 118
  · exact hroot.hOcc 122
  · exact hroot.hOcc 134
  · exact hroot.hOcc 157
  · exact hroot.hOcc 165
  · exact hroot.hOcc 196
  · exact hroot.hOcc 201
  · exact hroot.hOcc 211
  · exact hroot.hOcc 225
  · exact hroot.hOcc 233
  · exact hroot.hOcc 269
  · exact hroot.hOcc 277
  · exact hroot.hOcc 295
  · exact hroot.hOcc 297
  · exact hroot.hOcc 302
  · exact hroot.hOcc 313
  · exact hroot.hOcc 347
  · exact hroot.hOcc 381
  · exact hroot.hOcc 409
  · exact hroot.hOcc 440
  · exact hroot.hOcc 453
  · exact hroot.hOcc 457
  · exact hroot.hOcc 470
  · exact hroot.hOcc 472
  · exact hroot.hOcc 526
  · exact hroot.hOcc 569
  · exact hroot.hOcc 573
  · exact hroot.hOcc 604
  · exact hroot.hOcc 637
  · exact hroot.hOcc 645
  · exact hroot.hOcc 661
  · exact hroot.hOcc 665
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (39 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (7 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (28 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (40 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (29 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (19 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (36 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (45 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_45
  · change (∑ k, (if k = (10 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10

end QiushiMatmul
