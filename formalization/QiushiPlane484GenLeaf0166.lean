import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0166Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 127, .occ 142, .occ 144, .occ 161, .occ 233, .occ 497, .occ 780, .occ 1150, .occ 1154, .occ 1164, .occ 1166, .occ 1216, .occ 1232, .occ 1258, .occ 1262, .occ 1296, .occ 1357, .occ 1421, .occ 1458, .occ 1467, .occ 1520, .occ 1538, .occ 1548, .occ 1549, .occ 1608, .occ 1628, .occ 1629, .occ 1656, .occ 1659, .sumGe, .nonneg 3, .nonneg 24, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchGe 7 (1), .branchLe 18 (0), .branchGe 30 (1), .branchLe 20 (0), .branchGe 33 (1), .branchLe 13 (0), .branchLe 6 (0)]

def plane484GenLeaf0166Mult : Fin 44 → Nat := ![94450, 40512, 30792, 44517, 286517, 4975, 104718, 53614, 2368, 32957, 64659, 55287, 33842, 128637, 13535, 38664, 19492, 729, 63461, 24163, 43530, 51616, 37847, 25691, 84371, 18214, 83227, 11764, 21693, 6758, 304731, 175975, 5235, 160271, 304731, 286328, 304002, 627860, 199811, 448864, 271774, 695713, 101442, 255093]

theorem plane484GenLeaf0166 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_33 : (1 : Int) ≤ x 33)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0166Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0166Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0166Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0166Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 127
  · exact hroot.hOcc 142
  · exact hroot.hOcc 144
  · exact hroot.hOcc 161
  · exact hroot.hOcc 233
  · exact hroot.hOcc 497
  · exact hroot.hOcc 780
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1232
  · exact hroot.hOcc 1258
  · exact hroot.hOcc 1262
  · exact hroot.hOcc 1296
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1421
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1520
  · exact hroot.hOcc 1538
  · exact hroot.hOcc 1548
  · exact hroot.hOcc 1549
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1628
  · exact hroot.hOcc 1629
  · exact hroot.hOcc 1656
  · exact hroot.hOcc 1659
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (33 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_33
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6

end QiushiMatmul
