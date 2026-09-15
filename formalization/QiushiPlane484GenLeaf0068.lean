import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0068Refs : Fin 42 → RowRef 1665 43 := ![.occ 121, .occ 128, .occ 129, .occ 130, .occ 132, .occ 250, .occ 460, .occ 549, .occ 823, .occ 860, .occ 1148, .occ 1150, .occ 1168, .occ 1170, .occ 1173, .occ 1190, .occ 1191, .occ 1213, .occ 1214, .occ 1215, .occ 1216, .occ 1226, .occ 1459, .occ 1534, .occ 1537, .occ 1539, .occ 1559, .occ 1580, .occ 1602, .occ 1618, .occ 1626, .occ 1644, .sumGe, .nonneg 14, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchGe 13 (1), .branchLe 42 (0), .branchGe 0 (1), .branchGe 32 (1), .branchLe 33 (0)]

def plane484GenLeaf0068Mult : Fin 42 → Nat := ![274, 404, 2161, 617, 1300, 298, 66, 130, 66, 202, 648, 808, 218, 798, 342, 70, 223, 36, 532, 86, 590, 1059, 460, 259, 428, 841, 211, 192, 100, 948, 544, 129, 3642, 210, 3642, 3220, 2434, 4412, 3082, 3976, 4938, 3108]

theorem plane484GenLeaf0068 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0068Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0068Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0068Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0068Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 128
  · exact hroot.hOcc 129
  · exact hroot.hOcc 130
  · exact hroot.hOcc 132
  · exact hroot.hOcc 250
  · exact hroot.hOcc 460
  · exact hroot.hOcc 549
  · exact hroot.hOcc 823
  · exact hroot.hOcc 860
  · exact hroot.hOcc 1148
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1226
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1534
  · exact hroot.hOcc 1537
  · exact hroot.hOcc 1539
  · exact hroot.hOcc 1559
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1618
  · exact hroot.hOcc 1626
  · exact hroot.hOcc 1644
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (32 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32
  · change (∑ k, (if k = (33 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33

end QiushiMatmul
