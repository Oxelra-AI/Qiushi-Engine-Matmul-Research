import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0262Refs : Fin 44 → RowRef 1665 43 := ![.occ 92, .occ 135, .occ 136, .occ 151, .occ 283, .occ 578, .occ 670, .occ 854, .occ 859, .occ 860, .occ 874, .occ 1151, .occ 1154, .occ 1170, .occ 1183, .occ 1187, .occ 1188, .occ 1305, .occ 1391, .occ 1471, .occ 1472, .occ 1477, .occ 1481, .occ 1491, .occ 1561, .occ 1567, .occ 1609, .occ 1632, .occ 1638, .occ 1640, .occ 1641, .occ 1655, .sumGe, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchGe 29 (1), .branchLe 34 (0), .branchLe 13 (0), .branchLe 37 (0), .branchLe 10 (0), .branchLe 0 (0)]

def plane484GenLeaf0262Mult : Fin 44 → Nat := ![34236, 31834, 28226, 6750, 3825, 31978, 12319, 9930, 74211, 20119, 21484, 60596, 56567, 12271, 2151, 31826, 6320, 10269, 15379, 4919, 31616, 22268, 61044, 28909, 1106, 48374, 400, 6593, 37228, 43119, 17068, 1853, 208356, 110015, 201954, 161060, 176115, 200657, 169121, 179768, 117077, 151389, 178540, 195685]

theorem plane484GenLeaf0262 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0262Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0262Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0262Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0262Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 92
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 151
  · exact hroot.hOcc 283
  · exact hroot.hOcc 578
  · exact hroot.hOcc 670
  · exact hroot.hOcc 854
  · exact hroot.hOcc 859
  · exact hroot.hOcc 860
  · exact hroot.hOcc 874
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1305
  · exact hroot.hOcc 1391
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1561
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1632
  · exact hroot.hOcc 1638
  · exact hroot.hOcc 1640
  · exact hroot.hOcc 1641
  · exact hroot.hOcc 1655
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (37 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0

end QiushiMatmul
