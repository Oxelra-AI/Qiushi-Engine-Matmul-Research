import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0067Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 121, .occ 129, .occ 130, .occ 131, .occ 140, .occ 141, .occ 142, .occ 256, .occ 385, .occ 627, .occ 667, .occ 1147, .occ 1166, .occ 1168, .occ 1191, .occ 1214, .occ 1220, .occ 1254, .occ 1260, .occ 1303, .occ 1305, .occ 1319, .occ 1321, .occ 1353, .occ 1357, .occ 1458, .occ 1530, .occ 1534, .occ 1580, .occ 1602, .occ 1624, .occ 1650, .sumGe, .nonneg 25, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchGe 13 (1), .branchLe 42 (0), .branchGe 0 (1), .branchLe 32 (0), .branchGe 26 (1)]

def plane484GenLeaf0067Mult : Fin 44 → Nat := ![1872, 4534, 7835, 5022, 928, 2145, 6735, 9008, 12991, 1207, 5969, 5527, 2126, 1872, 1030, 1746, 2669, 1552, 3765, 28, 502, 1624, 1817, 450, 1590, 1350, 822, 450, 150, 1662, 350, 1206, 3036, 16075, 1520, 3492, 12203, 9944, 4252, 36765, 14903, 24275, 13383, 39045]

theorem plane484GenLeaf0067 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0067Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0067Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0067Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0067Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 121
  · exact hroot.hOcc 129
  · exact hroot.hOcc 130
  · exact hroot.hOcc 131
  · exact hroot.hOcc 140
  · exact hroot.hOcc 141
  · exact hroot.hOcc 142
  · exact hroot.hOcc 256
  · exact hroot.hOcc 385
  · exact hroot.hOcc 627
  · exact hroot.hOcc 667
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1254
  · exact hroot.hOcc 1260
  · exact hroot.hOcc 1303
  · exact hroot.hOcc 1305
  · exact hroot.hOcc 1319
  · exact hroot.hOcc 1321
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1530
  · exact hroot.hOcc 1534
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1624
  · exact hroot.hOcc 1650
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26

end QiushiMatmul
