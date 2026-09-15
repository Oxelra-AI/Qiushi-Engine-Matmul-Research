import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0205Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 122, .occ 130, .occ 132, .occ 140, .occ 142, .occ 196, .occ 201, .occ 208, .occ 210, .occ 840, .occ 1101, .occ 1133, .occ 1140, .occ 1154, .occ 1160, .occ 1164, .occ 1166, .occ 1173, .occ 1179, .occ 1214, .occ 1259, .occ 1328, .occ 1440, .occ 1458, .occ 1467, .occ 1478, .occ 1555, .occ 1591, .occ 1603, .sumGe, .nonneg 15, .nonneg 20, .nonneg 24, .branchLe 2 (0), .branchGe 29 (1), .branchGe 35 (1), .branchLe 16 (0), .branchLe 18 (0), .branchGe 1 (1), .branchGe 22 (1), .branchGe 0 (1), .branchLe 8 (0), .branchLe 19 (0)]

def plane484GenLeaf0205Mult : Fin 44 → Nat := ![313, 42, 251, 152, 364, 268, 70, 36, 136, 102, 188, 82, 20, 362, 17, 34, 161, 139, 219, 346, 82, 76, 108, 102, 32, 240, 285, 70, 36, 227, 886, 178, 142, 12, 886, 1302, 888, 510, 700, 1022, 1714, 878, 544, 790]

theorem plane484GenLeaf0205 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0205Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0205Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0205Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0205Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 122
  · exact hroot.hOcc 130
  · exact hroot.hOcc 132
  · exact hroot.hOcc 140
  · exact hroot.hOcc 142
  · exact hroot.hOcc 196
  · exact hroot.hOcc 201
  · exact hroot.hOcc 208
  · exact hroot.hOcc 210
  · exact hroot.hOcc 840
  · exact hroot.hOcc 1101
  · exact hroot.hOcc 1133
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1259
  · exact hroot.hOcc 1328
  · exact hroot.hOcc 1440
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1555
  · exact hroot.hOcc 1591
  · exact hroot.hOcc 1603
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19

end QiushiMatmul
