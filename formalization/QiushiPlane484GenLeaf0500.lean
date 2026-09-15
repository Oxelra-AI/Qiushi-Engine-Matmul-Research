import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0500Refs : Fin 41 → RowRef 1665 43 := ![.occ 126, .occ 127, .occ 131, .occ 140, .occ 325, .occ 442, .occ 683, .occ 708, .occ 748, .occ 822, .occ 844, .occ 858, .occ 978, .occ 1011, .occ 1188, .occ 1200, .occ 1206, .occ 1271, .occ 1407, .occ 1409, .occ 1467, .occ 1470, .occ 1471, .occ 1507, .occ 1509, .occ 1510, .occ 1512, .occ 1590, .occ 1636, .occ 1642, .sumGe, .nonneg 0, .nonneg 1, .nonneg 2, .nonneg 6, .branchGe 15 (1), .branchLe 35 (0), .branchGe 7 (1), .branchLe 32 (0), .branchGe 14 (1), .branchLe 3 (0)]

def plane484GenLeaf0500Mult : Fin 41 → Nat := ![1055, 1265, 788, 418, 241, 236, 719, 1265, 320, 330, 326, 33, 440, 63, 365, 55, 100, 408, 90, 811, 43, 10, 100, 236, 135, 191, 146, 167, 101, 109, 1475, 578, 628, 484, 4630, 3611, 1375, 6331, 1475, 5700, 420]

theorem plane484GenLeaf0500 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0500Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0500Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0500Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0500Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 126
  · exact hroot.hOcc 127
  · exact hroot.hOcc 131
  · exact hroot.hOcc 140
  · exact hroot.hOcc 325
  · exact hroot.hOcc 442
  · exact hroot.hOcc 683
  · exact hroot.hOcc 708
  · exact hroot.hOcc 748
  · exact hroot.hOcc 822
  · exact hroot.hOcc 844
  · exact hroot.hOcc 858
  · exact hroot.hOcc 978
  · exact hroot.hOcc 1011
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1271
  · exact hroot.hOcc 1407
  · exact hroot.hOcc 1409
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1507
  · exact hroot.hOcc 1509
  · exact hroot.hOcc 1510
  · exact hroot.hOcc 1512
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1636
  · exact hroot.hOcc 1642
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3

end QiushiMatmul
