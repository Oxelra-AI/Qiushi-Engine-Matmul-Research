import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0440Refs : Fin 41 → RowRef 1665 43 := ![.occ 128, .occ 131, .occ 133, .occ 135, .occ 138, .occ 204, .occ 289, .occ 335, .occ 861, .occ 961, .occ 967, .occ 971, .occ 1068, .occ 1087, .occ 1140, .occ 1170, .occ 1220, .occ 1307, .occ 1333, .occ 1343, .occ 1378, .occ 1384, .occ 1428, .occ 1477, .occ 1502, .occ 1524, .occ 1602, .occ 1642, .sumGe, .nonneg 0, .nonneg 1, .nonneg 23, .nonneg 24, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 29 (0), .branchGe 19 (1), .branchLe 31 (0), .branchGe 20 (1), .branchLe 9 (0)]

def plane484GenLeaf0440Mult : Fin 41 → Nat := ![85, 4743, 2825, 1918, 1863, 324, 481, 1026, 549, 1840, 341, 581, 1289, 1147, 314, 853, 887, 902, 478, 1290, 267, 481, 576, 2085, 18, 422, 1334, 481, 4743, 3074, 1115, 5169, 9151, 14320, 2258, 1883, 4429, 8724, 3409, 17892, 4265]

theorem plane484GenLeaf0440 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0440Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0440Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0440Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0440Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 128
  · exact hroot.hOcc 131
  · exact hroot.hOcc 133
  · exact hroot.hOcc 135
  · exact hroot.hOcc 138
  · exact hroot.hOcc 204
  · exact hroot.hOcc 289
  · exact hroot.hOcc 335
  · exact hroot.hOcc 861
  · exact hroot.hOcc 961
  · exact hroot.hOcc 967
  · exact hroot.hOcc 971
  · exact hroot.hOcc 1068
  · exact hroot.hOcc 1087
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1307
  · exact hroot.hOcc 1333
  · exact hroot.hOcc 1343
  · exact hroot.hOcc 1378
  · exact hroot.hOcc 1384
  · exact hroot.hOcc 1428
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1502
  · exact hroot.hOcc 1524
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1642
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (31 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20
  · change (∑ k, (if k = (9 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9

end QiushiMatmul
