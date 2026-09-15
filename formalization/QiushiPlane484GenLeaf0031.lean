import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0031Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 121, .occ 127, .occ 128, .occ 260, .occ 439, .occ 509, .occ 773, .occ 774, .occ 779, .occ 781, .occ 787, .occ 840, .occ 1164, .occ 1166, .occ 1196, .occ 1208, .occ 1268, .occ 1387, .occ 1388, .occ 1399, .occ 1408, .occ 1412, .occ 1444, .occ 1458, .occ 1472, .occ 1486, .occ 1606, .occ 1626, .occ 1663, .occ 1664, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchLe 17 (0), .branchGe 35 (1), .branchLe 25 (0), .branchLe 18 (0), .branchGe 42 (1), .branchGe 23 (1), .branchGe 7 (1)]

def plane484GenLeaf0031Mult : Fin 44 → Nat := ![24, 398, 566, 310, 152, 415, 122, 162, 32, 2372, 1079, 228, 467, 414, 151, 589, 311, 281, 254, 24, 156, 5, 1213, 73, 114, 673, 307, 384, 408, 702, 289, 2372, 2083, 1476, 1500, 742, 1860, 1262, 4668, 2004, 717, 5695, 2254, 7253]

theorem plane484GenLeaf0031 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0031Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0031Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0031Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0031Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 121
  · exact hroot.hOcc 127
  · exact hroot.hOcc 128
  · exact hroot.hOcc 260
  · exact hroot.hOcc 439
  · exact hroot.hOcc 509
  · exact hroot.hOcc 773
  · exact hroot.hOcc 774
  · exact hroot.hOcc 779
  · exact hroot.hOcc 781
  · exact hroot.hOcc 787
  · exact hroot.hOcc 840
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1268
  · exact hroot.hOcc 1387
  · exact hroot.hOcc 1388
  · exact hroot.hOcc 1399
  · exact hroot.hOcc 1408
  · exact hroot.hOcc 1412
  · exact hroot.hOcc 1444
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1626
  · exact hroot.hOcc 1663
  · exact hroot.hOcc 1664
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7

end QiushiMatmul
