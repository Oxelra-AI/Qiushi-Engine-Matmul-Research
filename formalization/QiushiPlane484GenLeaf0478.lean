import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0478Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 127, .occ 130, .occ 133, .occ 140, .occ 142, .occ 330, .occ 353, .occ 374, .occ 513, .occ 532, .occ 541, .occ 674, .occ 813, .occ 1046, .occ 1145, .occ 1159, .occ 1179, .occ 1200, .occ 1256, .occ 1393, .occ 1436, .occ 1477, .occ 1480, .occ 1483, .occ 1484, .occ 1590, .occ 1610, .occ 1612, .occ 1636, .sumGe, .nonneg 25, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchGe 0 (1), .branchLe 19 (0), .branchLe 3 (0), .branchGe 38 (1), .branchGe 34 (1), .branchLe 28 (0), .branchLe 32 (0), .branchLe 36 (0), .branchLe 8 (0)]

def plane484GenLeaf0478Mult : Fin 44 → Nat := ![1606, 290, 487, 1184, 1106, 1799, 1599, 1556, 539, 1262, 245, 453, 1672, 454, 89, 397, 119, 226, 1785, 55, 505, 107, 171, 534, 67, 734, 659, 461, 395, 119, 3636, 504, 10177, 2490, 2173, 2830, 853, 3149, 2106, 1678, 3108, 2902, 3346, 3241]

theorem plane484GenLeaf0478 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0478Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0478Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0478Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0478Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 127
  · exact hroot.hOcc 130
  · exact hroot.hOcc 133
  · exact hroot.hOcc 140
  · exact hroot.hOcc 142
  · exact hroot.hOcc 330
  · exact hroot.hOcc 353
  · exact hroot.hOcc 374
  · exact hroot.hOcc 513
  · exact hroot.hOcc 532
  · exact hroot.hOcc 541
  · exact hroot.hOcc 674
  · exact hroot.hOcc 813
  · exact hroot.hOcc 1046
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1159
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1256
  · exact hroot.hOcc 1393
  · exact hroot.hOcc 1436
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1480
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1612
  · exact hroot.hOcc 1636
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (38 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8

end QiushiMatmul
