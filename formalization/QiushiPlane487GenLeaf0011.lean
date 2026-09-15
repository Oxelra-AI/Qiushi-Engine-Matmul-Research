import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0011Refs : Fin 48 → RowRef 668 48 := ![.occ 83, .occ 86, .occ 93, .occ 102, .occ 106, .occ 118, .occ 119, .occ 123, .occ 127, .occ 157, .occ 191, .occ 197, .occ 219, .occ 220, .occ 240, .occ 258, .occ 263, .occ 269, .occ 303, .occ 312, .occ 313, .occ 315, .occ 361, .occ 386, .occ 396, .occ 399, .occ 414, .occ 444, .occ 458, .occ 468, .occ 530, .occ 554, .occ 577, .occ 604, .occ 639, .occ 660, .occ 662, .occ 666, .sumGe, .branchLe 39 (0), .branchLe 23 (0), .branchLe 6 (0), .branchLe 25 (0), .branchGe 12 (1), .branchLe 3 (0), .branchLe 24 (0), .branchLe 36 (0), .branchGe 17 (1)]

def plane487GenLeaf0011Mult : Fin 48 → Nat := ![908, 526, 789, 303, 367, 852, 438, 339, 207, 691, 701, 157, 396, 52, 147, 617, 152, 35, 825, 1012, 46, 193, 177, 1206, 112, 141, 192, 283, 199, 624, 301, 152, 66, 678, 193, 1, 224, 246, 2077, 1853, 1637, 1227, 1197, 3140, 736, 453, 1045, 5171]

theorem plane487GenLeaf0011 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0011Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0011Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0011Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0011Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 83
  · exact hroot.hOcc 86
  · exact hroot.hOcc 93
  · exact hroot.hOcc 102
  · exact hroot.hOcc 106
  · exact hroot.hOcc 118
  · exact hroot.hOcc 119
  · exact hroot.hOcc 123
  · exact hroot.hOcc 127
  · exact hroot.hOcc 157
  · exact hroot.hOcc 191
  · exact hroot.hOcc 197
  · exact hroot.hOcc 219
  · exact hroot.hOcc 220
  · exact hroot.hOcc 240
  · exact hroot.hOcc 258
  · exact hroot.hOcc 263
  · exact hroot.hOcc 269
  · exact hroot.hOcc 303
  · exact hroot.hOcc 312
  · exact hroot.hOcc 313
  · exact hroot.hOcc 315
  · exact hroot.hOcc 361
  · exact hroot.hOcc 386
  · exact hroot.hOcc 396
  · exact hroot.hOcc 399
  · exact hroot.hOcc 414
  · exact hroot.hOcc 444
  · exact hroot.hOcc 458
  · exact hroot.hOcc 468
  · exact hroot.hOcc 530
  · exact hroot.hOcc 554
  · exact hroot.hOcc 577
  · exact hroot.hOcc 604
  · exact hroot.hOcc 639
  · exact hroot.hOcc 660
  · exact hroot.hOcc 662
  · exact hroot.hOcc 666
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (6 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (25 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (12 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (3 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (24 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (36 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (17 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17

end QiushiMatmul
