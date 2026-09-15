import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0203Refs : Fin 43 → RowRef 1665 43 := ![.occ 122, .occ 128, .occ 139, .occ 141, .occ 144, .occ 220, .occ 224, .occ 226, .occ 512, .occ 559, .occ 884, .occ 1018, .occ 1133, .occ 1151, .occ 1179, .occ 1183, .occ 1214, .occ 1216, .occ 1260, .occ 1312, .occ 1357, .occ 1436, .occ 1467, .occ 1472, .occ 1485, .occ 1486, .occ 1550, .occ 1601, .occ 1603, .occ 1606, .sumGe, .nonneg 23, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchGe 35 (1), .branchLe 16 (0), .branchLe 18 (0), .branchGe 1 (1), .branchLe 22 (0), .branchGe 21 (1), .branchGe 31 (1), .branchGe 10 (1)]

def plane484GenLeaf0203Mult : Fin 43 → Nat := ![2087, 3059, 543, 367, 242, 312, 470, 711, 1697, 773, 924, 1571, 1452, 1488, 820, 1723, 598, 1115, 204, 1128, 1621, 952, 600, 717, 394, 440, 619, 139, 648, 1256, 5146, 207, 2475, 2589, 5804, 3455, 4603, 3108, 6460, 4058, 6703, 9820, 13851]

theorem plane484GenLeaf0203 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0203Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0203Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0203Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0203Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 122
  · exact hroot.hOcc 128
  · exact hroot.hOcc 139
  · exact hroot.hOcc 141
  · exact hroot.hOcc 144
  · exact hroot.hOcc 220
  · exact hroot.hOcc 224
  · exact hroot.hOcc 226
  · exact hroot.hOcc 512
  · exact hroot.hOcc 559
  · exact hroot.hOcc 884
  · exact hroot.hOcc 1018
  · exact hroot.hOcc 1133
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1260
  · exact hroot.hOcc 1312
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1436
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1485
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1550
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1606
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21
  · change (∑ k, (if k = (31 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10

end QiushiMatmul
