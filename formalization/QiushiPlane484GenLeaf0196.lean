import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0196Refs : Fin 39 → RowRef 1665 43 := ![.occ 120, .occ 124, .occ 132, .occ 136, .occ 138, .occ 201, .occ 210, .occ 363, .occ 376, .occ 390, .occ 470, .occ 656, .occ 704, .occ 810, .occ 1025, .occ 1044, .occ 1140, .occ 1154, .occ 1236, .occ 1345, .occ 1348, .occ 1388, .occ 1440, .occ 1472, .occ 1526, .occ 1540, .sumGe, .nonneg 0, .nonneg 2, .nonneg 16, .nonneg 17, .nonneg 18, .branchLe 15 (0), .branchGe 29 (1), .branchGe 35 (1), .branchGe 5 (1), .branchGe 22 (1), .branchGe 19 (1), .branchGe 24 (1)]

def plane484GenLeaf0196Mult : Fin 39 → Nat := ![18, 30, 48, 60, 12, 22, 10, 25, 12, 21, 19, 38, 7, 6, 28, 37, 17, 31, 12, 18, 5, 3, 2, 12, 29, 10, 60, 6, 42, 96, 48, 46, 46, 176, 87, 240, 126, 229, 170]

theorem plane484GenLeaf0196 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0196Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0196Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0196Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0196Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 124
  · exact hroot.hOcc 132
  · exact hroot.hOcc 136
  · exact hroot.hOcc 138
  · exact hroot.hOcc 201
  · exact hroot.hOcc 210
  · exact hroot.hOcc 363
  · exact hroot.hOcc 376
  · exact hroot.hOcc 390
  · exact hroot.hOcc 470
  · exact hroot.hOcc 656
  · exact hroot.hOcc 704
  · exact hroot.hOcc 810
  · exact hroot.hOcc 1025
  · exact hroot.hOcc 1044
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1236
  · exact hroot.hOcc 1345
  · exact hroot.hOcc 1348
  · exact hroot.hOcc 1388
  · exact hroot.hOcc 1440
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1526
  · exact hroot.hOcc 1540
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24

end QiushiMatmul
