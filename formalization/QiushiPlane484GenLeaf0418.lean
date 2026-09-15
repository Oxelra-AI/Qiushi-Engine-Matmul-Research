import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0418Refs : Fin 42 → RowRef 1665 43 := ![.occ 119, .occ 121, .occ 124, .occ 126, .occ 127, .occ 142, .occ 146, .occ 154, .occ 213, .occ 233, .occ 437, .occ 442, .occ 707, .occ 860, .occ 926, .occ 945, .occ 1161, .occ 1164, .occ 1227, .occ 1269, .occ 1373, .occ 1486, .occ 1491, .occ 1492, .occ 1567, .occ 1590, .occ 1628, .occ 1632, .sumGe, .nonneg 10, .nonneg 24, .branchLe 15 (0), .branchGe 2 (1), .branchGe 7 (1), .branchLe 6 (0), .branchGe 31 (1), .branchGe 29 (1), .branchLe 36 (0), .branchLe 34 (0), .branchLe 8 (0), .branchLe 20 (0), .branchLe 40 (0)]

def plane484GenLeaf0418Mult : Fin 42 → Nat := ![326, 1823, 4349, 2463, 2037, 2196, 256, 5884, 820, 1910, 1180, 522, 1334, 1032, 758, 476, 2076, 2680, 516, 516, 652, 2832, 1068, 888, 2212, 548, 1272, 1900, 8612, 1032, 1272, 5868, 5200, 22640, 256, 5772, 8712, 7544, 8612, 5606, 6246, 8064]

theorem plane484GenLeaf0418 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0418Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0418Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0418Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0418Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 124
  · exact hroot.hOcc 126
  · exact hroot.hOcc 127
  · exact hroot.hOcc 142
  · exact hroot.hOcc 146
  · exact hroot.hOcc 154
  · exact hroot.hOcc 213
  · exact hroot.hOcc 233
  · exact hroot.hOcc 437
  · exact hroot.hOcc 442
  · exact hroot.hOcc 707
  · exact hroot.hOcc 860
  · exact hroot.hOcc 926
  · exact hroot.hOcc 945
  · exact hroot.hOcc 1161
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1227
  · exact hroot.hOcc 1269
  · exact hroot.hOcc 1373
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1628
  · exact hroot.hOcc 1632
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (31 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (40 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40

end QiushiMatmul
