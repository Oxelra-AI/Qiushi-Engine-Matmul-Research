import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0482Refs : Fin 42 → RowRef 1665 43 := ![.occ 120, .occ 129, .occ 131, .occ 133, .occ 140, .occ 142, .occ 170, .occ 186, .occ 287, .occ 348, .occ 573, .occ 662, .occ 664, .occ 691, .occ 693, .occ 762, .occ 1146, .occ 1158, .occ 1186, .occ 1188, .occ 1206, .occ 1266, .occ 1334, .occ 1350, .occ 1358, .occ 1458, .occ 1483, .occ 1610, .occ 1621, .occ 1630, .sumGe, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchGe 0 (1), .branchLe 19 (0), .branchLe 25 (0), .branchLe 3 (0), .branchGe 38 (1), .branchGe 34 (1), .branchGe 28 (1), .branchLe 29 (0)]

def plane484GenLeaf0482Mult : Fin 42 → Nat := ![45, 41, 39, 64, 313, 245, 74, 358, 5, 279, 89, 206, 145, 406, 569, 211, 13, 15, 13, 311, 219, 44, 7, 181, 127, 26, 359, 26, 270, 74, 696, 3424, 52, 385, 112, 310, 180, 482, 1420, 1070, 2035, 696]

theorem plane484GenLeaf0482 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0482Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0482Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0482Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0482Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 129
  · exact hroot.hOcc 131
  · exact hroot.hOcc 133
  · exact hroot.hOcc 140
  · exact hroot.hOcc 142
  · exact hroot.hOcc 170
  · exact hroot.hOcc 186
  · exact hroot.hOcc 287
  · exact hroot.hOcc 348
  · exact hroot.hOcc 573
  · exact hroot.hOcc 662
  · exact hroot.hOcc 664
  · exact hroot.hOcc 691
  · exact hroot.hOcc 693
  · exact hroot.hOcc 762
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1266
  · exact hroot.hOcc 1334
  · exact hroot.hOcc 1350
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1621
  · exact hroot.hOcc 1630
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (38 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29

end QiushiMatmul
