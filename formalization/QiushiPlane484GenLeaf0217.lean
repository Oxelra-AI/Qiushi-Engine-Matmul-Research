import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0217Refs : Fin 34 → RowRef 1665 43 := ![.occ 134, .occ 136, .occ 142, .occ 156, .occ 183, .occ 242, .occ 323, .occ 379, .occ 396, .occ 460, .occ 591, .occ 822, .occ 1096, .occ 1159, .occ 1222, .occ 1236, .occ 1258, .occ 1287, .occ 1328, .occ 1380, .occ 1425, .occ 1471, .occ 1481, .occ 1533, .occ 1636, .occ 1656, .sumGe, .nonneg 25, .branchLe 2 (0), .branchGe 29 (1), .branchGe 35 (1), .branchGe 16 (1), .branchLe 37 (0), .branchGe 22 (1)]

def plane484GenLeaf0217Mult : Fin 34 → Nat := ![68, 9, 99, 17, 9, 12, 80, 64, 53, 12, 75, 23, 75, 51, 3, 96, 14, 48, 35, 25, 27, 37, 55, 9, 6, 45, 150, 186, 80, 541, 492, 793, 74, 198]

theorem plane484GenLeaf0217 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0217Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0217Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0217Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0217Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 134
  · exact hroot.hOcc 136
  · exact hroot.hOcc 142
  · exact hroot.hOcc 156
  · exact hroot.hOcc 183
  · exact hroot.hOcc 242
  · exact hroot.hOcc 323
  · exact hroot.hOcc 379
  · exact hroot.hOcc 396
  · exact hroot.hOcc 460
  · exact hroot.hOcc 591
  · exact hroot.hOcc 822
  · exact hroot.hOcc 1096
  · exact hroot.hOcc 1159
  · exact hroot.hOcc 1222
  · exact hroot.hOcc 1236
  · exact hroot.hOcc 1258
  · exact hroot.hOcc 1287
  · exact hroot.hOcc 1328
  · exact hroot.hOcc 1380
  · exact hroot.hOcc 1425
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1533
  · exact hroot.hOcc 1636
  · exact hroot.hOcc 1656
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (37 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22

end QiushiMatmul
