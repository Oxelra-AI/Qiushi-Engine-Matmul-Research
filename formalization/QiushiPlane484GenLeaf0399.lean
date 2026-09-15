import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0399Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 121, .occ 123, .occ 124, .occ 126, .occ 134, .occ 137, .occ 138, .occ 139, .occ 259, .occ 442, .occ 508, .occ 931, .occ 1164, .occ 1174, .occ 1180, .occ 1191, .occ 1196, .occ 1215, .occ 1224, .occ 1295, .occ 1307, .occ 1383, .occ 1405, .occ 1459, .occ 1462, .occ 1489, .occ 1524, .occ 1532, .occ 1567, .occ 1608, .occ 1637, .sumGe, .nonneg 10, .branchLe 15 (0), .branchGe 2 (1), .branchGe 7 (1), .branchLe 6 (0), .branchLe 31 (0), .branchLe 24 (0), .branchGe 37 (1), .branchLe 0 (0), .branchLe 4 (0), .branchLe 35 (0)]

def plane484GenLeaf0399Mult : Fin 44 → Nat := ![6836, 109322, 12166, 112174, 182748, 31752, 71604, 44952, 22692, 5260, 21724, 13616, 21784, 50047, 81120, 125536, 21236, 131176, 14669, 49516, 61432, 80, 11000, 22008, 3885, 97228, 121580, 4476, 87216, 6728, 68487, 36480, 360668, 65430, 279236, 505712, 614282, 143746, 277512, 50496, 474120, 235298, 143746, 360668]

theorem plane484GenLeaf0399 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0399Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0399Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0399Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0399Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 123
  · exact hroot.hOcc 124
  · exact hroot.hOcc 126
  · exact hroot.hOcc 134
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 139
  · exact hroot.hOcc 259
  · exact hroot.hOcc 442
  · exact hroot.hOcc 508
  · exact hroot.hOcc 931
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1180
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1224
  · exact hroot.hOcc 1295
  · exact hroot.hOcc 1307
  · exact hroot.hOcc 1383
  · exact hroot.hOcc 1405
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1524
  · exact hroot.hOcc 1532
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1637
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (31 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35

end QiushiMatmul
