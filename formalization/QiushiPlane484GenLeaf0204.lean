import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0204Refs : Fin 43 → RowRef 1665 43 := ![.occ 127, .occ 128, .occ 133, .occ 140, .occ 220, .occ 286, .occ 309, .occ 437, .occ 473, .occ 633, .occ 840, .occ 860, .occ 861, .occ 1133, .occ 1140, .occ 1151, .occ 1166, .occ 1179, .occ 1187, .occ 1205, .occ 1214, .occ 1265, .occ 1377, .occ 1417, .occ 1458, .occ 1467, .occ 1472, .occ 1486, .occ 1555, .occ 1563, .occ 1607, .occ 1649, .sumGe, .nonneg 15, .nonneg 20, .branchLe 2 (0), .branchGe 29 (1), .branchGe 35 (1), .branchLe 16 (0), .branchLe 18 (0), .branchGe 1 (1), .branchGe 22 (1), .branchLe 0 (0)]

def plane484GenLeaf0204Mult : Fin 43 → Nat := ![574, 2, 72, 716, 242, 300, 40, 196, 440, 56, 34, 154, 586, 92, 542, 40, 24, 660, 63, 213, 502, 110, 6, 104, 2, 149, 582, 393, 6, 6, 6, 42, 1242, 232, 212, 786, 1814, 2442, 1046, 1046, 3686, 1556, 1212]

theorem plane484GenLeaf0204 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0204Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0204Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0204Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0204Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 127
  · exact hroot.hOcc 128
  · exact hroot.hOcc 133
  · exact hroot.hOcc 140
  · exact hroot.hOcc 220
  · exact hroot.hOcc 286
  · exact hroot.hOcc 309
  · exact hroot.hOcc 437
  · exact hroot.hOcc 473
  · exact hroot.hOcc 633
  · exact hroot.hOcc 840
  · exact hroot.hOcc 860
  · exact hroot.hOcc 861
  · exact hroot.hOcc 1133
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1265
  · exact hroot.hOcc 1377
  · exact hroot.hOcc 1417
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1555
  · exact hroot.hOcc 1563
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1649
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0

end QiushiMatmul
