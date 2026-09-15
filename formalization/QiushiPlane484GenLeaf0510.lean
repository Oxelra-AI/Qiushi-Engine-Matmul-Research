import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0510Refs : Fin 43 → RowRef 1665 43 := ![.occ 121, .occ 125, .occ 128, .occ 133, .occ 138, .occ 140, .occ 289, .occ 330, .occ 472, .occ 549, .occ 800, .occ 852, .occ 1075, .occ 1076, .occ 1159, .occ 1236, .occ 1280, .occ 1334, .occ 1349, .occ 1358, .occ 1397, .occ 1411, .occ 1484, .occ 1528, .occ 1534, .occ 1536, .occ 1609, .occ 1610, .occ 1611, .occ 1615, .occ 1658, .sumGe, .nonneg 0, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchLe 30 (0), .branchLe 34 (0), .branchLe 8 (0), .branchLe 33 (0), .branchGe 5 (1), .branchLe 10 (0), .branchGe 41 (1)]

def plane484GenLeaf0510Mult : Fin 43 → Nat := ![537, 483, 2043, 1858, 3092, 1516, 1985, 178, 112, 220, 82, 1596, 3132, 1384, 718, 212, 852, 964, 482, 1334, 112, 502, 494, 3026, 714, 620, 1234, 1234, 356, 2040, 100, 6054, 1040, 16092, 3550, 112, 6054, 5236, 502, 6054, 13590, 706, 9916]

theorem plane484GenLeaf0510 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_41 : (1 : Int) ≤ x 41)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0510Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0510Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0510Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0510Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 125
  · exact hroot.hOcc 128
  · exact hroot.hOcc 133
  · exact hroot.hOcc 138
  · exact hroot.hOcc 140
  · exact hroot.hOcc 289
  · exact hroot.hOcc 330
  · exact hroot.hOcc 472
  · exact hroot.hOcc 549
  · exact hroot.hOcc 800
  · exact hroot.hOcc 852
  · exact hroot.hOcc 1075
  · exact hroot.hOcc 1076
  · exact hroot.hOcc 1159
  · exact hroot.hOcc 1236
  · exact hroot.hOcc 1280
  · exact hroot.hOcc 1334
  · exact hroot.hOcc 1349
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1397
  · exact hroot.hOcc 1411
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1528
  · exact hroot.hOcc 1534
  · exact hroot.hOcc 1536
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1611
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1658
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (33 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (41 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_41

end QiushiMatmul
