import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0082Refs : Fin 50 → RowRef 726 49 := ![.occ 78, .occ 85, .occ 87, .occ 98, .occ 111, .occ 118, .occ 123, .occ 140, .occ 142, .occ 144, .occ 149, .occ 170, .occ 201, .occ 234, .occ 235, .occ 240, .occ 266, .occ 308, .occ 312, .occ 351, .occ 359, .occ 379, .occ 393, .occ 401, .occ 410, .occ 421, .occ 431, .occ 482, .occ 484, .occ 501, .occ 517, .occ 559, .occ 582, .occ 585, .occ 606, .occ 640, .occ 664, .occ 680, .occ 696, .occ 720, .occ 721, .occ 722, .sumGe, .nonneg 43, .branchGe 31 (1), .branchLe 44 (0), .branchLe 11 (0), .branchLe 27 (0), .branchGe 22 (1), .branchGe 3 (1)]

def plane491GenLeaf0082Mult : Fin 50 → Nat := ![75, 1420, 801, 544, 1103, 1116, 685, 77, 746, 236, 358, 188, 694, 52, 233, 979, 1074, 14, 505, 9, 241, 916, 46, 100, 494, 394, 522, 243, 11, 235, 617, 154, 388, 63, 121, 212, 168, 208, 5, 297, 619, 157, 1976, 90, 5308, 1390, 1606, 1522, 5469, 5408]

theorem plane491GenLeaf0082 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0082Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0082Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0082Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0082Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 78
  · exact hroot.hOcc 85
  · exact hroot.hOcc 87
  · exact hroot.hOcc 98
  · exact hroot.hOcc 111
  · exact hroot.hOcc 118
  · exact hroot.hOcc 123
  · exact hroot.hOcc 140
  · exact hroot.hOcc 142
  · exact hroot.hOcc 144
  · exact hroot.hOcc 149
  · exact hroot.hOcc 170
  · exact hroot.hOcc 201
  · exact hroot.hOcc 234
  · exact hroot.hOcc 235
  · exact hroot.hOcc 240
  · exact hroot.hOcc 266
  · exact hroot.hOcc 308
  · exact hroot.hOcc 312
  · exact hroot.hOcc 351
  · exact hroot.hOcc 359
  · exact hroot.hOcc 379
  · exact hroot.hOcc 393
  · exact hroot.hOcc 401
  · exact hroot.hOcc 410
  · exact hroot.hOcc 421
  · exact hroot.hOcc 431
  · exact hroot.hOcc 482
  · exact hroot.hOcc 484
  · exact hroot.hOcc 501
  · exact hroot.hOcc 517
  · exact hroot.hOcc 559
  · exact hroot.hOcc 582
  · exact hroot.hOcc 585
  · exact hroot.hOcc 606
  · exact hroot.hOcc 640
  · exact hroot.hOcc 664
  · exact hroot.hOcc 680
  · exact hroot.hOcc 696
  · exact hroot.hOcc 720
  · exact hroot.hOcc 721
  · exact hroot.hOcc 722
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (43 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 43
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (11 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (22 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22
  · change (∑ k, (if k = (3 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3

end QiushiMatmul
