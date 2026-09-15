import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0011Refs : Fin 44 → RowRef 713 43 := ![.occ 103, .occ 104, .occ 109, .occ 113, .occ 135, .occ 139, .occ 197, .occ 209, .occ 211, .occ 234, .occ 238, .occ 239, .occ 247, .occ 258, .occ 283, .occ 295, .occ 297, .occ 354, .occ 362, .occ 438, .occ 467, .occ 468, .occ 494, .occ 519, .occ 539, .occ 547, .occ 599, .occ 632, .occ 635, .occ 649, .occ 666, .occ 667, .occ 683, .occ 690, .occ 692, .sumGe, .branchLe 29 (0), .branchLe 4 (0), .branchLe 23 (0), .branchLe 16 (0), .branchGe 39 (1), .branchLe 17 (0), .branchGe 22 (1), .branchLe 30 (0)]

def plane490GenLeaf0011Mult : Fin 44 → Nat := ![57, 63, 35, 62, 162, 86, 8, 10, 73, 48, 33, 17, 116, 2, 92, 16, 37, 8, 129, 37, 26, 1, 58, 25, 8, 23, 58, 37, 12, 21, 26, 44, 38, 18, 32, 253, 137, 237, 253, 99, 22, 190, 887, 98]

theorem plane490GenLeaf0011 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0011Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0011Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0011Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0011Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 103
  · exact hroot.hOcc 104
  · exact hroot.hOcc 109
  · exact hroot.hOcc 113
  · exact hroot.hOcc 135
  · exact hroot.hOcc 139
  · exact hroot.hOcc 197
  · exact hroot.hOcc 209
  · exact hroot.hOcc 211
  · exact hroot.hOcc 234
  · exact hroot.hOcc 238
  · exact hroot.hOcc 239
  · exact hroot.hOcc 247
  · exact hroot.hOcc 258
  · exact hroot.hOcc 283
  · exact hroot.hOcc 295
  · exact hroot.hOcc 297
  · exact hroot.hOcc 354
  · exact hroot.hOcc 362
  · exact hroot.hOcc 438
  · exact hroot.hOcc 467
  · exact hroot.hOcc 468
  · exact hroot.hOcc 494
  · exact hroot.hOcc 519
  · exact hroot.hOcc 539
  · exact hroot.hOcc 547
  · exact hroot.hOcc 599
  · exact hroot.hOcc 632
  · exact hroot.hOcc 635
  · exact hroot.hOcc 649
  · exact hroot.hOcc 666
  · exact hroot.hOcc 667
  · exact hroot.hOcc 683
  · exact hroot.hOcc 690
  · exact hroot.hOcc 692
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (39 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30

end QiushiMatmul
