import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0222Refs : Fin 44 → RowRef 1665 43 := ![.occ 121, .occ 136, .occ 137, .occ 139, .occ 226, .occ 323, .occ 368, .occ 379, .occ 487, .occ 556, .occ 593, .occ 615, .occ 1140, .occ 1159, .occ 1160, .occ 1174, .occ 1179, .occ 1190, .occ 1216, .occ 1222, .occ 1258, .occ 1299, .occ 1328, .occ 1345, .occ 1348, .occ 1459, .occ 1481, .occ 1506, .occ 1546, .occ 1548, .occ 1559, .occ 1580, .occ 1615, .occ 1662, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchGe 35 (1), .branchGe 16 (1), .branchGe 37 (1), .branchGe 17 (1), .branchLe 20 (0), .branchGe 32 (1)]

def plane484GenLeaf0222Mult : Fin 44 → Nat := ![10800, 6991, 1080, 20259, 25577, 15193, 944, 28094, 55179, 1825, 41138, 7596, 1632, 17797, 2012, 6773, 5584, 202, 5400, 14243, 7418, 9572, 3211, 9169, 8565, 2481, 30324, 6279, 14825, 6396, 4118, 7852, 10955, 11621, 55381, 15008, 16784, 113229, 191941, 124491, 96257, 125438, 38426, 180048]

theorem plane484GenLeaf0222 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0222Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0222Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0222Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0222Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 139
  · exact hroot.hOcc 226
  · exact hroot.hOcc 323
  · exact hroot.hOcc 368
  · exact hroot.hOcc 379
  · exact hroot.hOcc 487
  · exact hroot.hOcc 556
  · exact hroot.hOcc 593
  · exact hroot.hOcc 615
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1159
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1222
  · exact hroot.hOcc 1258
  · exact hroot.hOcc 1299
  · exact hroot.hOcc 1328
  · exact hroot.hOcc 1345
  · exact hroot.hOcc 1348
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1506
  · exact hroot.hOcc 1546
  · exact hroot.hOcc 1548
  · exact hroot.hOcc 1559
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1662
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (32 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32

end QiushiMatmul
