import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0101Refs : Fin 39 → RowRef 1665 43 := ![.occ 119, .occ 127, .occ 131, .occ 132, .occ 138, .occ 139, .occ 140, .occ 281, .occ 289, .occ 340, .occ 357, .occ 384, .occ 827, .occ 891, .occ 963, .occ 1143, .occ 1145, .occ 1150, .occ 1254, .occ 1393, .occ 1444, .occ 1462, .occ 1547, .occ 1620, .occ 1639, .occ 1663, .sumGe, .nonneg 1, .nonneg 2, .nonneg 7, .branchLe 15 (0), .branchLe 29 (0), .branchGe 4 (1), .branchLe 36 (0), .branchGe 26 (1), .branchGe 37 (1), .branchLe 34 (0), .branchLe 16 (0), .branchGe 12 (1)]

def plane484GenLeaf0101Mult : Fin 39 → Nat := ![190, 114, 35, 5, 66, 75, 13, 26, 180, 40, 86, 134, 74, 30, 34, 10, 30, 84, 80, 84, 84, 84, 36, 22, 62, 30, 282, 88, 66, 382, 84, 282, 950, 198, 418, 410, 242, 110, 624]

theorem plane484GenLeaf0101 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0101Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0101Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0101Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0101Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 127
  · exact hroot.hOcc 131
  · exact hroot.hOcc 132
  · exact hroot.hOcc 138
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 281
  · exact hroot.hOcc 289
  · exact hroot.hOcc 340
  · exact hroot.hOcc 357
  · exact hroot.hOcc 384
  · exact hroot.hOcc 827
  · exact hroot.hOcc 891
  · exact hroot.hOcc 963
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1254
  · exact hroot.hOcc 1393
  · exact hroot.hOcc 1444
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1547
  · exact hroot.hOcc 1620
  · exact hroot.hOcc 1639
  · exact hroot.hOcc 1663
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (12 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12

end QiushiMatmul
