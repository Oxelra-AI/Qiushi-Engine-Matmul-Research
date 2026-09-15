import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0037Refs : Fin 44 → RowRef 713 43 := ![.occ 84, .occ 91, .occ 102, .occ 106, .occ 109, .occ 120, .occ 198, .occ 201, .occ 205, .occ 219, .occ 279, .occ 280, .occ 284, .occ 292, .occ 295, .occ 302, .occ 303, .occ 314, .occ 375, .occ 447, .occ 494, .occ 500, .occ 518, .occ 533, .occ 545, .occ 575, .occ 639, .occ 668, .occ 679, .occ 686, .occ 689, .occ 692, .occ 704, .occ 710, .sumGe, .branchLe 29 (0), .branchLe 4 (0), .branchGe 23 (1), .branchLe 30 (0), .branchLe 28 (0), .branchLe 35 (0), .branchGe 5 (1), .branchLe 19 (0), .branchLe 39 (0)]

def plane490GenLeaf0037Mult : Fin 44 → Nat := ![18246, 15425, 32255, 17297, 59254, 50639, 11546, 29379, 11611, 3404, 18376, 2980, 17856, 11743, 21766, 32869, 30059, 6664, 35437, 31373, 2424, 20062, 9211, 27150, 6685, 1854, 6390, 8409, 3476, 2166, 27820, 32196, 1301, 4938, 113685, 111519, 89753, 12487, 95398, 34221, 85865, 219701, 96479, 76947]

theorem plane490GenLeaf0037 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0037Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0037Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0037Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0037Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 84
  · exact hroot.hOcc 91
  · exact hroot.hOcc 102
  · exact hroot.hOcc 106
  · exact hroot.hOcc 109
  · exact hroot.hOcc 120
  · exact hroot.hOcc 198
  · exact hroot.hOcc 201
  · exact hroot.hOcc 205
  · exact hroot.hOcc 219
  · exact hroot.hOcc 279
  · exact hroot.hOcc 280
  · exact hroot.hOcc 284
  · exact hroot.hOcc 292
  · exact hroot.hOcc 295
  · exact hroot.hOcc 302
  · exact hroot.hOcc 303
  · exact hroot.hOcc 314
  · exact hroot.hOcc 375
  · exact hroot.hOcc 447
  · exact hroot.hOcc 494
  · exact hroot.hOcc 500
  · exact hroot.hOcc 518
  · exact hroot.hOcc 533
  · exact hroot.hOcc 545
  · exact hroot.hOcc 575
  · exact hroot.hOcc 639
  · exact hroot.hOcc 668
  · exact hroot.hOcc 679
  · exact hroot.hOcc 686
  · exact hroot.hOcc 689
  · exact hroot.hOcc 692
  · exact hroot.hOcc 704
  · exact hroot.hOcc 710
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39

end QiushiMatmul
