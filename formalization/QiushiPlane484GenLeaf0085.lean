import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0085Refs : Fin 42 → RowRef 1665 43 := ![.occ 119, .occ 122, .occ 127, .occ 130, .occ 134, .occ 356, .occ 384, .occ 424, .occ 814, .occ 856, .occ 1143, .occ 1145, .occ 1160, .occ 1237, .occ 1246, .occ 1256, .occ 1278, .occ 1284, .occ 1300, .occ 1351, .occ 1379, .occ 1429, .occ 1439, .occ 1449, .occ 1478, .occ 1531, .occ 1547, .occ 1609, .occ 1620, .occ 1626, .occ 1639, .occ 1655, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchGe 4 (1), .branchLe 36 (0), .branchLe 26 (0), .branchLe 24 (0), .branchLe 19 (0), .branchLe 31 (0)]

def plane484GenLeaf0085Mult : Fin 42 → Nat := ![48832, 15529, 41639, 47482, 34682, 21738, 7082, 18016, 13808, 12322, 20203, 9661, 10928, 5030, 2369, 10154, 6014, 17341, 17858, 5570, 30831, 11327, 5066, 24630, 40285, 8372, 14154, 22911, 13566, 5139, 29448, 16723, 148858, 143792, 89546, 137930, 280942, 148858, 91690, 79100, 135292, 124228]

theorem plane484GenLeaf0085 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0085Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0085Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0085Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0085Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 122
  · exact hroot.hOcc 127
  · exact hroot.hOcc 130
  · exact hroot.hOcc 134
  · exact hroot.hOcc 356
  · exact hroot.hOcc 384
  · exact hroot.hOcc 424
  · exact hroot.hOcc 814
  · exact hroot.hOcc 856
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1237
  · exact hroot.hOcc 1246
  · exact hroot.hOcc 1256
  · exact hroot.hOcc 1278
  · exact hroot.hOcc 1284
  · exact hroot.hOcc 1300
  · exact hroot.hOcc 1351
  · exact hroot.hOcc 1379
  · exact hroot.hOcc 1429
  · exact hroot.hOcc 1439
  · exact hroot.hOcc 1449
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1531
  · exact hroot.hOcc 1547
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1620
  · exact hroot.hOcc 1626
  · exact hroot.hOcc 1639
  · exact hroot.hOcc 1655
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (31 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31

end QiushiMatmul
