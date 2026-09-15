import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0543Refs : Fin 43 → RowRef 1665 43 := ![.occ 120, .occ 129, .occ 130, .occ 132, .occ 133, .occ 135, .occ 142, .occ 180, .occ 196, .occ 220, .occ 224, .occ 277, .occ 295, .occ 679, .occ 1158, .occ 1160, .occ 1170, .occ 1173, .occ 1183, .occ 1227, .occ 1330, .occ 1340, .occ 1357, .occ 1371, .occ 1401, .occ 1409, .occ 1417, .occ 1446, .occ 1472, .occ 1486, .occ 1488, .occ 1615, .sumGe, .nonneg 16, .nonneg 20, .nonneg 25, .branchGe 15 (1), .branchGe 35 (1), .branchLe 26 (0), .branchGe 30 (1), .branchLe 1 (0), .branchGe 0 (1), .branchGe 21 (1)]

def plane484GenLeaf0543Mult : Fin 43 → Nat := ![225, 488, 229, 263, 700, 824, 976, 95, 437, 20, 65, 389, 1177, 358, 257, 365, 721, 204, 263, 124, 218, 250, 365, 115, 78, 186, 18, 506, 22, 9, 261, 257, 1452, 38, 617, 2419, 4110, 3340, 476, 3818, 730, 2898, 4323]

theorem plane484GenLeaf0543 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0543Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0543Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0543Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0543Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 129
  · exact hroot.hOcc 130
  · exact hroot.hOcc 132
  · exact hroot.hOcc 133
  · exact hroot.hOcc 135
  · exact hroot.hOcc 142
  · exact hroot.hOcc 180
  · exact hroot.hOcc 196
  · exact hroot.hOcc 220
  · exact hroot.hOcc 224
  · exact hroot.hOcc 277
  · exact hroot.hOcc 295
  · exact hroot.hOcc 679
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1227
  · exact hroot.hOcc 1330
  · exact hroot.hOcc 1340
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1371
  · exact hroot.hOcc 1401
  · exact hroot.hOcc 1409
  · exact hroot.hOcc 1417
  · exact hroot.hOcc 1446
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1615
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21

end QiushiMatmul
