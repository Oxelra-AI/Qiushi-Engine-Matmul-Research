import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0421Refs : Fin 44 → RowRef 1665 43 := ![.occ 123, .occ 125, .occ 126, .occ 127, .occ 128, .occ 129, .occ 135, .occ 137, .occ 139, .occ 145, .occ 146, .occ 148, .occ 156, .occ 216, .occ 325, .occ 442, .occ 782, .occ 784, .occ 1164, .occ 1186, .occ 1187, .occ 1217, .occ 1302, .occ 1373, .occ 1481, .occ 1484, .occ 1486, .occ 1590, .occ 1608, .occ 1641, .occ 1643, .occ 1649, .sumGe, .nonneg 9, .nonneg 10, .branchLe 15 (0), .branchGe 2 (1), .branchGe 7 (1), .branchLe 6 (0), .branchGe 31 (1), .branchGe 29 (1), .branchLe 36 (0), .branchLe 34 (0), .branchGe 8 (1)]

def plane484GenLeaf0421Mult : Fin 44 → Nat := ![305, 1132, 716, 37, 583, 330, 188, 349, 620, 202, 34, 160, 65, 468, 18, 207, 459, 68, 619, 707, 463, 362, 490, 234, 58, 136, 558, 868, 1343, 577, 526, 748, 2856, 1182, 326, 1069, 2877, 3656, 194, 3946, 2753, 2393, 2856, 5555]

theorem plane484GenLeaf0421 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0421Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0421Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0421Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0421Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 123
  · exact hroot.hOcc 125
  · exact hroot.hOcc 126
  · exact hroot.hOcc 127
  · exact hroot.hOcc 128
  · exact hroot.hOcc 129
  · exact hroot.hOcc 135
  · exact hroot.hOcc 137
  · exact hroot.hOcc 139
  · exact hroot.hOcc 145
  · exact hroot.hOcc 146
  · exact hroot.hOcc 148
  · exact hroot.hOcc 156
  · exact hroot.hOcc 216
  · exact hroot.hOcc 325
  · exact hroot.hOcc 442
  · exact hroot.hOcc 782
  · exact hroot.hOcc 784
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1217
  · exact hroot.hOcc 1302
  · exact hroot.hOcc 1373
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1641
  · exact hroot.hOcc 1643
  · exact hroot.hOcc 1649
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (9 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 9
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (31 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8

end QiushiMatmul
