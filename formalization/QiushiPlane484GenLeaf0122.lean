import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0122Refs : Fin 43 → RowRef 1665 43 := ![.occ 120, .occ 121, .occ 125, .occ 128, .occ 129, .occ 132, .occ 192, .occ 206, .occ 385, .occ 706, .occ 707, .occ 789, .occ 1021, .occ 1025, .occ 1073, .occ 1136, .occ 1145, .occ 1154, .occ 1230, .occ 1259, .occ 1290, .occ 1315, .occ 1362, .occ 1381, .occ 1455, .occ 1477, .occ 1517, .occ 1538, .occ 1548, .occ 1622, .occ 1636, .occ 1656, .sumGe, .nonneg 9, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 39 (0), .branchLe 32 (0), .branchLe 28 (0), .branchGe 5 (1)]

def plane484GenLeaf0122Mult : Fin 43 → Nat := ![54279, 9381, 33052, 7401, 24953, 9744, 26662, 966, 6420, 26694, 924, 87906, 8272, 6786, 52604, 2748, 11482, 55366, 4388, 33422, 1836, 11734, 12758, 5480, 2552, 13416, 14230, 19940, 24328, 9924, 5976, 23346, 115330, 7346, 105406, 64820, 305806, 81908, 7346, 83260, 109850, 113494, 394644]

theorem plane484GenLeaf0122 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0122Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0122Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0122Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0122Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 121
  · exact hroot.hOcc 125
  · exact hroot.hOcc 128
  · exact hroot.hOcc 129
  · exact hroot.hOcc 132
  · exact hroot.hOcc 192
  · exact hroot.hOcc 206
  · exact hroot.hOcc 385
  · exact hroot.hOcc 706
  · exact hroot.hOcc 707
  · exact hroot.hOcc 789
  · exact hroot.hOcc 1021
  · exact hroot.hOcc 1025
  · exact hroot.hOcc 1073
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1230
  · exact hroot.hOcc 1259
  · exact hroot.hOcc 1290
  · exact hroot.hOcc 1315
  · exact hroot.hOcc 1362
  · exact hroot.hOcc 1381
  · exact hroot.hOcc 1455
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1517
  · exact hroot.hOcc 1538
  · exact hroot.hOcc 1548
  · exact hroot.hOcc 1622
  · exact hroot.hOcc 1636
  · exact hroot.hOcc 1656
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (9 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 9
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5

end QiushiMatmul
