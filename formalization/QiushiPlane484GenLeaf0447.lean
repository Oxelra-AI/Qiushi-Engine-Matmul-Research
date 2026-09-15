import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0447Refs : Fin 43 → RowRef 1665 43 := ![.occ 105, .occ 121, .occ 123, .occ 128, .occ 131, .occ 133, .occ 138, .occ 145, .occ 377, .occ 434, .occ 464, .occ 627, .occ 649, .occ 700, .occ 804, .occ 806, .occ 1094, .occ 1147, .occ 1188, .occ 1264, .occ 1270, .occ 1304, .occ 1358, .occ 1459, .occ 1544, .occ 1615, .occ 1631, .occ 1647, .occ 1658, .occ 1661, .sumGe, .nonneg 0, .nonneg 1, .nonneg 2, .nonneg 19, .branchGe 15 (1), .branchLe 35 (0), .branchLe 29 (0), .branchGe 23 (1), .branchLe 10 (0), .branchGe 3 (1), .branchLe 33 (0), .branchLe 20 (0)]

def plane484GenLeaf0447Mult : Fin 43 → Nat := ![483, 291, 204, 456, 686, 528, 781, 354, 340, 181, 176, 157, 88, 160, 393, 329, 107, 470, 111, 154, 9, 83, 286, 34, 28, 224, 182, 83, 369, 117, 1279, 388, 581, 370, 1350, 3004, 1042, 1279, 2584, 623, 2828, 1279, 593]

theorem plane484GenLeaf0447 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0447Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0447Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0447Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0447Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 105
  · exact hroot.hOcc 121
  · exact hroot.hOcc 123
  · exact hroot.hOcc 128
  · exact hroot.hOcc 131
  · exact hroot.hOcc 133
  · exact hroot.hOcc 138
  · exact hroot.hOcc 145
  · exact hroot.hOcc 377
  · exact hroot.hOcc 434
  · exact hroot.hOcc 464
  · exact hroot.hOcc 627
  · exact hroot.hOcc 649
  · exact hroot.hOcc 700
  · exact hroot.hOcc 804
  · exact hroot.hOcc 806
  · exact hroot.hOcc 1094
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1264
  · exact hroot.hOcc 1270
  · exact hroot.hOcc 1304
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1544
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1631
  · exact hroot.hOcc 1647
  · exact hroot.hOcc 1658
  · exact hroot.hOcc 1661
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3
  · change (∑ k, (if k = (33 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20

end QiushiMatmul
