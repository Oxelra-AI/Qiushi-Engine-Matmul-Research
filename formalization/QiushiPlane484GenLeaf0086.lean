import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0086Refs : Fin 43 → RowRef 1665 43 := ![.occ 119, .occ 125, .occ 127, .occ 130, .occ 134, .occ 152, .occ 153, .occ 194, .occ 198, .occ 355, .occ 356, .occ 423, .occ 994, .occ 1028, .occ 1145, .occ 1150, .occ 1154, .occ 1160, .occ 1268, .occ 1277, .occ 1340, .occ 1371, .occ 1442, .occ 1448, .occ 1510, .occ 1547, .occ 1610, .occ 1615, .occ 1649, .occ 1655, .occ 1663, .sumGe, .nonneg 23, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchGe 4 (1), .branchLe 36 (0), .branchLe 26 (0), .branchLe 24 (0), .branchLe 19 (0), .branchGe 31 (1), .branchLe 41 (0)]

def plane484GenLeaf0086Mult : Fin 43 → Nat := ![3267, 12189, 21322, 23499, 2851, 15115, 2409, 16107, 6648, 6253, 11896, 783, 7921, 1032, 5091, 16526, 5630, 14014, 2064, 221, 10480, 9448, 22830, 8502, 221, 6085, 6662, 908, 21382, 1032, 20393, 68743, 2030, 47907, 51463, 27717, 156873, 68743, 62658, 43259, 51996, 50186, 61049]

theorem plane484GenLeaf0086 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_41 : x 41 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0086Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0086Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0086Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0086Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 125
  · exact hroot.hOcc 127
  · exact hroot.hOcc 130
  · exact hroot.hOcc 134
  · exact hroot.hOcc 152
  · exact hroot.hOcc 153
  · exact hroot.hOcc 194
  · exact hroot.hOcc 198
  · exact hroot.hOcc 355
  · exact hroot.hOcc 356
  · exact hroot.hOcc 423
  · exact hroot.hOcc 994
  · exact hroot.hOcc 1028
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1268
  · exact hroot.hOcc 1277
  · exact hroot.hOcc 1340
  · exact hroot.hOcc 1371
  · exact hroot.hOcc 1442
  · exact hroot.hOcc 1448
  · exact hroot.hOcc 1510
  · exact hroot.hOcc 1547
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1649
  · exact hroot.hOcc 1655
  · exact hroot.hOcc 1663
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (31 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (41 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_41

end QiushiMatmul
