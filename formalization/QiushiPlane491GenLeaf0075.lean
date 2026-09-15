import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0075Refs : Fin 50 → RowRef 726 49 := ![.occ 94, .occ 98, .occ 102, .occ 104, .occ 110, .occ 118, .occ 119, .occ 131, .occ 167, .occ 170, .occ 175, .occ 201, .occ 219, .occ 234, .occ 243, .occ 312, .occ 315, .occ 332, .occ 335, .occ 350, .occ 359, .occ 367, .occ 369, .occ 379, .occ 389, .occ 393, .occ 431, .occ 484, .occ 490, .occ 491, .occ 525, .occ 526, .occ 565, .occ 570, .occ 606, .occ 611, .occ 626, .occ 664, .occ 669, .occ 699, .occ 711, .occ 718, .sumGe, .branchGe 31 (1), .branchLe 44 (0), .branchLe 11 (0), .branchLe 27 (0), .branchLe 22 (0), .branchLe 15 (0), .branchGe 12 (1)]

def plane491GenLeaf0075Mult : Fin 50 → Nat := ![54363, 14263, 10437, 1471, 7708, 51749, 22845, 21305, 9576, 25001, 42972, 3991, 26960, 4317, 9006, 7488, 11406, 12144, 22199, 10897, 2472, 4910, 16094, 2038, 15731, 50259, 3755, 6241, 424, 1038, 2815, 15146, 18166, 5414, 3892, 13780, 3805, 2903, 14717, 1688, 16508, 4158, 73455, 224522, 69650, 68259, 44973, 64759, 38357, 165517]

theorem plane491GenLeaf0075 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0075Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0075Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0075Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0075Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 94
  · exact hroot.hOcc 98
  · exact hroot.hOcc 102
  · exact hroot.hOcc 104
  · exact hroot.hOcc 110
  · exact hroot.hOcc 118
  · exact hroot.hOcc 119
  · exact hroot.hOcc 131
  · exact hroot.hOcc 167
  · exact hroot.hOcc 170
  · exact hroot.hOcc 175
  · exact hroot.hOcc 201
  · exact hroot.hOcc 219
  · exact hroot.hOcc 234
  · exact hroot.hOcc 243
  · exact hroot.hOcc 312
  · exact hroot.hOcc 315
  · exact hroot.hOcc 332
  · exact hroot.hOcc 335
  · exact hroot.hOcc 350
  · exact hroot.hOcc 359
  · exact hroot.hOcc 367
  · exact hroot.hOcc 369
  · exact hroot.hOcc 379
  · exact hroot.hOcc 389
  · exact hroot.hOcc 393
  · exact hroot.hOcc 431
  · exact hroot.hOcc 484
  · exact hroot.hOcc 490
  · exact hroot.hOcc 491
  · exact hroot.hOcc 525
  · exact hroot.hOcc 526
  · exact hroot.hOcc 565
  · exact hroot.hOcc 570
  · exact hroot.hOcc 606
  · exact hroot.hOcc 611
  · exact hroot.hOcc 626
  · exact hroot.hOcc 664
  · exact hroot.hOcc 669
  · exact hroot.hOcc 699
  · exact hroot.hOcc 711
  · exact hroot.hOcc 718
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (11 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (22 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (15 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (12 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12

end QiushiMatmul
