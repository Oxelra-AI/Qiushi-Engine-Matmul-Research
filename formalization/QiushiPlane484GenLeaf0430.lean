import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0430Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 123, .occ 125, .occ 128, .occ 135, .occ 139, .occ 140, .occ 189, .occ 297, .occ 299, .occ 733, .occ 846, .occ 861, .occ 877, .occ 971, .occ 1136, .occ 1174, .occ 1188, .occ 1270, .occ 1298, .occ 1325, .occ 1330, .occ 1358, .occ 1371, .occ 1409, .occ 1414, .occ 1422, .occ 1437, .occ 1483, .occ 1525, .occ 1630, .occ 1651, .occ 1659, .sumGe, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 0 (0), .branchLe 29 (0), .branchLe 23 (0), .branchLe 19 (0), .branchLe 40 (0), .branchGe 28 (1), .branchLe 37 (0)]

def plane484GenLeaf0430Mult : Fin 44 → Nat := ![8647, 18660, 13928, 12124, 15760, 2053, 43857, 4717, 24511, 979, 2892, 5510, 10188, 2688, 4766, 10299, 6263, 17589, 2053, 19676, 4237, 1565, 26799, 7387, 15238, 10102, 2184, 1628, 22264, 10102, 8033, 5683, 18473, 88201, 121577, 65937, 62463, 23983, 76337, 86148, 86148, 80168, 72184, 81938]

theorem plane484GenLeaf0430 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0430Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0430Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0430Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0430Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 123
  · exact hroot.hOcc 125
  · exact hroot.hOcc 128
  · exact hroot.hOcc 135
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 189
  · exact hroot.hOcc 297
  · exact hroot.hOcc 299
  · exact hroot.hOcc 733
  · exact hroot.hOcc 846
  · exact hroot.hOcc 861
  · exact hroot.hOcc 877
  · exact hroot.hOcc 971
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1270
  · exact hroot.hOcc 1298
  · exact hroot.hOcc 1325
  · exact hroot.hOcc 1330
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1371
  · exact hroot.hOcc 1409
  · exact hroot.hOcc 1414
  · exact hroot.hOcc 1422
  · exact hroot.hOcc 1437
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1525
  · exact hroot.hOcc 1630
  · exact hroot.hOcc 1651
  · exact hroot.hOcc 1659
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (40 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (37 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37

end QiushiMatmul
