import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0049Refs : Fin 49 → RowRef 668 48 := ![.occ 85, .occ 103, .occ 118, .occ 135, .occ 160, .occ 202, .occ 222, .occ 225, .occ 231, .occ 235, .occ 246, .occ 254, .occ 260, .occ 294, .occ 300, .occ 306, .occ 323, .occ 341, .occ 343, .occ 347, .occ 351, .occ 364, .occ 379, .occ 386, .occ 467, .occ 469, .occ 498, .occ 536, .occ 563, .occ 587, .occ 589, .occ 627, .occ 650, .occ 656, .sumGe, .nonneg 7, .branchGe 39 (1), .branchLe 28 (0), .branchLe 40 (0), .branchLe 29 (0), .branchLe 19 (0), .branchLe 36 (0), .branchLe 23 (0), .branchLe 45 (0), .branchLe 5 (0), .branchLe 25 (0), .branchLe 30 (0), .branchGe 2 (1), .branchGe 21 (1)]

def plane487GenLeaf0049Mult : Fin 49 → Nat := ![13020, 8791, 9998, 10541, 36577, 19176, 9656, 6772, 6746, 3831, 8409, 751, 17834, 9609, 5658, 7823, 11991, 995, 5628, 11839, 5843, 4571, 4251, 12998, 9637, 5592, 2270, 4611, 2633, 11838, 969, 1191, 8791, 7862, 42671, 6559, 61688, 25062, 14011, 40401, 31793, 19460, 32577, 42671, 18428, 28708, 26400, 32388, 129727]

theorem plane487GenLeaf0049 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_45 : x 45 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0049Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0049Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0049Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0049Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 85
  · exact hroot.hOcc 103
  · exact hroot.hOcc 118
  · exact hroot.hOcc 135
  · exact hroot.hOcc 160
  · exact hroot.hOcc 202
  · exact hroot.hOcc 222
  · exact hroot.hOcc 225
  · exact hroot.hOcc 231
  · exact hroot.hOcc 235
  · exact hroot.hOcc 246
  · exact hroot.hOcc 254
  · exact hroot.hOcc 260
  · exact hroot.hOcc 294
  · exact hroot.hOcc 300
  · exact hroot.hOcc 306
  · exact hroot.hOcc 323
  · exact hroot.hOcc 341
  · exact hroot.hOcc 343
  · exact hroot.hOcc 347
  · exact hroot.hOcc 351
  · exact hroot.hOcc 364
  · exact hroot.hOcc 379
  · exact hroot.hOcc 386
  · exact hroot.hOcc 467
  · exact hroot.hOcc 469
  · exact hroot.hOcc 498
  · exact hroot.hOcc 536
  · exact hroot.hOcc 563
  · exact hroot.hOcc 587
  · exact hroot.hOcc 589
  · exact hroot.hOcc 627
  · exact hroot.hOcc 650
  · exact hroot.hOcc 656
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (39 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (28 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (40 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (29 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (19 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (36 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (45 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_45
  · change (∑ k, (if k = (5 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (25 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (30 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (2 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (21 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21

end QiushiMatmul
