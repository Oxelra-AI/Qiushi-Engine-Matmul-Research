import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0133Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 125, .occ 127, .occ 132, .occ 134, .occ 141, .occ 164, .occ 254, .occ 476, .occ 575, .occ 582, .occ 625, .occ 628, .occ 721, .occ 828, .occ 933, .occ 946, .occ 1070, .occ 1168, .occ 1170, .occ 1179, .occ 1213, .occ 1394, .occ 1421, .occ 1431, .occ 1448, .occ 1538, .occ 1542, .occ 1557, .occ 1623, .occ 1629, .occ 1641, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 39 (0), .branchGe 32 (1), .branchLe 37 (0), .branchLe 3 (0), .branchGe 12 (1), .branchGe 25 (1)]

def plane484GenLeaf0133Mult : Fin 44 → Nat := ![902, 115, 140, 70, 682, 266, 113, 223, 768, 514, 932, 264, 895, 168, 510, 143, 323, 70, 42, 15, 209, 277, 183, 19, 506, 432, 266, 475, 55, 212, 199, 79, 1507, 540, 1313, 3633, 794, 644, 1507, 3921, 1507, 728, 3259, 4057]

theorem plane484GenLeaf0133 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0133Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0133Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0133Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0133Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 125
  · exact hroot.hOcc 127
  · exact hroot.hOcc 132
  · exact hroot.hOcc 134
  · exact hroot.hOcc 141
  · exact hroot.hOcc 164
  · exact hroot.hOcc 254
  · exact hroot.hOcc 476
  · exact hroot.hOcc 575
  · exact hroot.hOcc 582
  · exact hroot.hOcc 625
  · exact hroot.hOcc 628
  · exact hroot.hOcc 721
  · exact hroot.hOcc 828
  · exact hroot.hOcc 933
  · exact hroot.hOcc 946
  · exact hroot.hOcc 1070
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1394
  · exact hroot.hOcc 1421
  · exact hroot.hOcc 1431
  · exact hroot.hOcc 1448
  · exact hroot.hOcc 1538
  · exact hroot.hOcc 1542
  · exact hroot.hOcc 1557
  · exact hroot.hOcc 1623
  · exact hroot.hOcc 1629
  · exact hroot.hOcc 1641
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (32 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32
  · change (∑ k, (if k = (37 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (12 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25

end QiushiMatmul
