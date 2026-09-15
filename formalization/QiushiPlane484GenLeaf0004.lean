import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0004Refs : Fin 44 → RowRef 1665 43 := ![.occ 122, .occ 128, .occ 129, .occ 132, .occ 142, .occ 258, .occ 287, .occ 318, .occ 319, .occ 338, .occ 564, .occ 715, .occ 1146, .occ 1196, .occ 1223, .occ 1244, .occ 1289, .occ 1325, .occ 1353, .occ 1356, .occ 1364, .occ 1434, .occ 1451, .occ 1477, .occ 1580, .occ 1608, .occ 1622, .occ 1626, .occ 1628, .occ 1651, .occ 1655, .sumGe, .nonneg 40, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchLe 17 (0), .branchLe 35 (0), .branchLe 41 (0), .branchGe 8 (1), .branchLe 9 (0), .branchLe 19 (0)]

def plane484GenLeaf0004Mult : Fin 44 → Nat := ![31650, 28365, 84271, 2622, 34087, 4012, 27118, 12714, 15365, 907, 5509, 2085, 20958, 25074, 15417, 22097, 27734, 13023, 1804, 8029, 5326, 70291, 60600, 4181, 20477, 74535, 1434, 16542, 16958, 51265, 75754, 228650, 14276, 133835, 182618, 225412, 31123, 37746, 158221, 228650, 126618, 364757, 195150, 211692]

theorem plane484GenLeaf0004 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hUB_41 : x 41 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0004Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0004Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0004Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0004Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 122
  · exact hroot.hOcc 128
  · exact hroot.hOcc 129
  · exact hroot.hOcc 132
  · exact hroot.hOcc 142
  · exact hroot.hOcc 258
  · exact hroot.hOcc 287
  · exact hroot.hOcc 318
  · exact hroot.hOcc 319
  · exact hroot.hOcc 338
  · exact hroot.hOcc 564
  · exact hroot.hOcc 715
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1223
  · exact hroot.hOcc 1244
  · exact hroot.hOcc 1289
  · exact hroot.hOcc 1325
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1356
  · exact hroot.hOcc 1364
  · exact hroot.hOcc 1434
  · exact hroot.hOcc 1451
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1622
  · exact hroot.hOcc 1626
  · exact hroot.hOcc 1628
  · exact hroot.hOcc 1651
  · exact hroot.hOcc 1655
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (40 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (41 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_41
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8
  · change (∑ k, (if k = (9 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19

end QiushiMatmul
