import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0199Refs : Fin 43 → RowRef 1665 43 := ![.occ 120, .occ 127, .occ 196, .occ 345, .occ 412, .occ 437, .occ 703, .occ 704, .occ 707, .occ 861, .occ 1140, .occ 1151, .occ 1154, .occ 1166, .occ 1170, .occ 1179, .occ 1206, .occ 1214, .occ 1326, .occ 1390, .occ 1398, .occ 1472, .occ 1478, .occ 1492, .occ 1500, .occ 1502, .occ 1505, .occ 1506, .occ 1561, .occ 1606, .occ 1610, .occ 1623, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchGe 35 (1), .branchLe 16 (0), .branchLe 18 (0), .branchGe 1 (1), .branchLe 22 (0), .branchLe 21 (0), .branchGe 6 (1)]

def plane484GenLeaf0199Mult : Fin 43 → Nat := ![1444, 38018, 13664, 328, 28442, 18330, 6630, 4520, 8540, 32454, 23594, 7000, 2680, 16094, 1224, 16094, 2814, 23728, 2070, 6145, 9261, 21722, 472, 11464, 4242, 5591, 4960, 5239, 4820, 22138, 6742, 21762, 77944, 75130, 66480, 123388, 110580, 77944, 36658, 90632, 51198, 44262, 118840]

theorem plane484GenLeaf0199 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0199Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0199Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0199Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0199Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 127
  · exact hroot.hOcc 196
  · exact hroot.hOcc 345
  · exact hroot.hOcc 412
  · exact hroot.hOcc 437
  · exact hroot.hOcc 703
  · exact hroot.hOcc 704
  · exact hroot.hOcc 707
  · exact hroot.hOcc 861
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1326
  · exact hroot.hOcc 1390
  · exact hroot.hOcc 1398
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1500
  · exact hroot.hOcc 1502
  · exact hroot.hOcc 1505
  · exact hroot.hOcc 1506
  · exact hroot.hOcc 1561
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1623
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (21 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6

end QiushiMatmul
