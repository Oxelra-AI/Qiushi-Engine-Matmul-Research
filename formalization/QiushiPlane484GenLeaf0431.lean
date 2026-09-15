import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0431Refs : Fin 41 → RowRef 1665 43 := ![.occ 120, .occ 121, .occ 122, .occ 125, .occ 135, .occ 140, .occ 142, .occ 273, .occ 312, .occ 488, .occ 551, .occ 595, .occ 599, .occ 1043, .occ 1075, .occ 1174, .occ 1188, .occ 1206, .occ 1298, .occ 1311, .occ 1343, .occ 1350, .occ 1409, .occ 1446, .occ 1483, .occ 1567, .occ 1609, .occ 1610, .occ 1615, .occ 1645, .occ 1659, .sumGe, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 29 (0), .branchLe 23 (0), .branchLe 19 (0), .branchLe 40 (0), .branchGe 28 (1), .branchGe 37 (1)]

def plane484GenLeaf0431Mult : Fin 41 → Nat := ![7524, 138, 7129, 3431, 2602, 12452, 6806, 8515, 12623, 7738, 5171, 1927, 11391, 2615, 568, 2892, 4946, 5588, 1632, 5937, 3021, 518, 1553, 4007, 6155, 941, 740, 740, 12000, 10124, 389, 28199, 66032, 16456, 16588, 27258, 28199, 28199, 27681, 56428, 58796]

theorem plane484GenLeaf0431 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0431Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0431Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0431Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0431Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 125
  · exact hroot.hOcc 135
  · exact hroot.hOcc 140
  · exact hroot.hOcc 142
  · exact hroot.hOcc 273
  · exact hroot.hOcc 312
  · exact hroot.hOcc 488
  · exact hroot.hOcc 551
  · exact hroot.hOcc 595
  · exact hroot.hOcc 599
  · exact hroot.hOcc 1043
  · exact hroot.hOcc 1075
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1298
  · exact hroot.hOcc 1311
  · exact hroot.hOcc 1343
  · exact hroot.hOcc 1350
  · exact hroot.hOcc 1409
  · exact hroot.hOcc 1446
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1645
  · exact hroot.hOcc 1659
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (40 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37

end QiushiMatmul
