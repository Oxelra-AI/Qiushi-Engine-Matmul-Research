import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0033Refs : Fin 49 → RowRef 668 48 := ![.occ 86, .occ 88, .occ 89, .occ 90, .occ 111, .occ 153, .occ 156, .occ 219, .occ 223, .occ 224, .occ 231, .occ 233, .occ 240, .occ 242, .occ 246, .occ 253, .occ 270, .occ 294, .occ 296, .occ 303, .occ 347, .occ 352, .occ 381, .occ 386, .occ 390, .occ 391, .occ 399, .occ 402, .occ 446, .occ 471, .occ 591, .occ 599, .occ 609, .occ 650, .occ 657, .occ 658, .occ 665, .sumGe, .nonneg 0, .nonneg 25, .nonneg 26, .nonneg 45, .branchLe 39 (0), .branchLe 23 (0), .branchGe 6 (1), .branchGe 33 (1), .branchLe 12 (0), .branchLe 42 (0), .branchGe 36 (1)]

def plane487GenLeaf0033Mult : Fin 49 → Nat := ![8484, 801, 8848, 5379, 7200, 3522, 2756, 909, 1964, 652, 6327, 1074, 7358, 907, 2795, 9250, 8008, 6800, 14719, 9090, 5383, 1166, 3525, 5343, 4594, 254, 5383, 1040, 4483, 2926, 920, 945, 2743, 162, 1727, 2671, 821, 20102, 2490, 4662, 2580, 1040, 17392, 17430, 24833, 21246, 19940, 4831, 55989]

theorem plane487GenLeaf0033 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_33 : (1 : Int) ≤ x 33)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0033Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0033Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0033Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0033Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 86
  · exact hroot.hOcc 88
  · exact hroot.hOcc 89
  · exact hroot.hOcc 90
  · exact hroot.hOcc 111
  · exact hroot.hOcc 153
  · exact hroot.hOcc 156
  · exact hroot.hOcc 219
  · exact hroot.hOcc 223
  · exact hroot.hOcc 224
  · exact hroot.hOcc 231
  · exact hroot.hOcc 233
  · exact hroot.hOcc 240
  · exact hroot.hOcc 242
  · exact hroot.hOcc 246
  · exact hroot.hOcc 253
  · exact hroot.hOcc 270
  · exact hroot.hOcc 294
  · exact hroot.hOcc 296
  · exact hroot.hOcc 303
  · exact hroot.hOcc 347
  · exact hroot.hOcc 352
  · exact hroot.hOcc 381
  · exact hroot.hOcc 386
  · exact hroot.hOcc 390
  · exact hroot.hOcc 391
  · exact hroot.hOcc 399
  · exact hroot.hOcc 402
  · exact hroot.hOcc 446
  · exact hroot.hOcc 471
  · exact hroot.hOcc 591
  · exact hroot.hOcc 599
  · exact hroot.hOcc 609
  · exact hroot.hOcc 650
  · exact hroot.hOcc 657
  · exact hroot.hOcc 658
  · exact hroot.hOcc 665
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (25 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (26 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (45 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (6 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (33 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_33
  · change (∑ k, (if k = (12 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (42 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (36 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36

end QiushiMatmul
