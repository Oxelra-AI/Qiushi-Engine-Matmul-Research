import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0007Refs : Fin 50 → RowRef 726 49 := ![.occ 78, .occ 80, .occ 107, .occ 111, .occ 115, .occ 122, .occ 147, .occ 188, .occ 221, .occ 230, .occ 236, .occ 257, .occ 287, .occ 306, .occ 315, .occ 327, .occ 332, .occ 355, .occ 377, .occ 384, .occ 392, .occ 410, .occ 414, .occ 486, .occ 511, .occ 552, .occ 559, .occ 573, .occ 576, .occ 590, .occ 594, .occ 612, .occ 616, .occ 647, .occ 686, .occ 707, .occ 712, .sumGe, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchLe 29 (0), .branchLe 46 (0), .branchLe 32 (0), .branchLe 38 (0), .branchGe 6 (1), .branchLe 0 (0), .branchLe 43 (0), .branchLe 41 (0), .branchGe 9 (1)]

def plane491GenLeaf0007Mult : Fin 50 → Nat := ![206805, 135410, 147463, 2065, 6428, 15017, 23229, 33292, 138316, 26088, 84585, 10284, 174435, 1319, 40728, 16930, 12885, 12891, 209237, 71218, 9158, 186635, 61872, 187988, 45436, 80900, 61780, 22237, 85528, 18175, 94838, 1511, 12302, 147302, 49633, 185124, 42134, 522023, 492202, 405224, 394818, 192428, 232891, 428821, 336899, 796059, 302807, 328772, 271584, 606584]

theorem plane491GenLeaf0007 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_46 : x 46 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_41 : x 41 ≤ (0 : Int))
    (hUB_43 : x 43 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0007Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0007Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0007Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0007Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 78
  · exact hroot.hOcc 80
  · exact hroot.hOcc 107
  · exact hroot.hOcc 111
  · exact hroot.hOcc 115
  · exact hroot.hOcc 122
  · exact hroot.hOcc 147
  · exact hroot.hOcc 188
  · exact hroot.hOcc 221
  · exact hroot.hOcc 230
  · exact hroot.hOcc 236
  · exact hroot.hOcc 257
  · exact hroot.hOcc 287
  · exact hroot.hOcc 306
  · exact hroot.hOcc 315
  · exact hroot.hOcc 327
  · exact hroot.hOcc 332
  · exact hroot.hOcc 355
  · exact hroot.hOcc 377
  · exact hroot.hOcc 384
  · exact hroot.hOcc 392
  · exact hroot.hOcc 410
  · exact hroot.hOcc 414
  · exact hroot.hOcc 486
  · exact hroot.hOcc 511
  · exact hroot.hOcc 552
  · exact hroot.hOcc 559
  · exact hroot.hOcc 573
  · exact hroot.hOcc 576
  · exact hroot.hOcc 590
  · exact hroot.hOcc 594
  · exact hroot.hOcc 612
  · exact hroot.hOcc 616
  · exact hroot.hOcc 647
  · exact hroot.hOcc 686
  · exact hroot.hOcc 707
  · exact hroot.hOcc 712
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (46 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_46
  · change (∑ k, (if k = (32 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (38 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (6 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (0 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (43 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (41 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_41
  · change (∑ k, (if k = (9 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9

end QiushiMatmul
