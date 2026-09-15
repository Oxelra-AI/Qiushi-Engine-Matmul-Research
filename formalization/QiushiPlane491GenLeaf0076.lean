import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0076Refs : Fin 50 → RowRef 726 49 := ![.occ 98, .occ 107, .occ 118, .occ 127, .occ 175, .occ 219, .occ 234, .occ 244, .occ 257, .occ 288, .occ 315, .occ 320, .occ 329, .occ 334, .occ 335, .occ 340, .occ 393, .occ 402, .occ 418, .occ 467, .occ 484, .occ 490, .occ 495, .occ 514, .occ 519, .occ 565, .occ 574, .occ 575, .occ 582, .occ 606, .occ 621, .occ 622, .occ 640, .occ 643, .occ 687, .occ 694, .occ 711, .occ 714, .occ 715, .occ 717, .sumGe, .nonneg 16, .branchGe 31 (1), .branchLe 44 (0), .branchLe 11 (0), .branchLe 27 (0), .branchLe 22 (0), .branchGe 15 (1), .branchLe 48 (0), .branchLe 38 (0)]

def plane491GenLeaf0076Mult : Fin 50 → Nat := ![347072, 55654, 595837, 69305, 413450, 320220, 411775, 82891, 84921, 112878, 225112, 162559, 642631, 247631, 223456, 77941, 672466, 8424, 316129, 2496, 266242, 68943, 6588, 152452, 121213, 162676, 110154, 155497, 454478, 232014, 302026, 17009, 345774, 34928, 205640, 27247, 208692, 9169, 103573, 155554, 1532081, 272631, 4445738, 1094798, 1350567, 1411499, 1367415, 1142618, 1027237, 825432]

theorem plane491GenLeaf0076 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_48 : x 48 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_38 : x 38 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0076Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0076Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0076Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0076Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 98
  · exact hroot.hOcc 107
  · exact hroot.hOcc 118
  · exact hroot.hOcc 127
  · exact hroot.hOcc 175
  · exact hroot.hOcc 219
  · exact hroot.hOcc 234
  · exact hroot.hOcc 244
  · exact hroot.hOcc 257
  · exact hroot.hOcc 288
  · exact hroot.hOcc 315
  · exact hroot.hOcc 320
  · exact hroot.hOcc 329
  · exact hroot.hOcc 334
  · exact hroot.hOcc 335
  · exact hroot.hOcc 340
  · exact hroot.hOcc 393
  · exact hroot.hOcc 402
  · exact hroot.hOcc 418
  · exact hroot.hOcc 467
  · exact hroot.hOcc 484
  · exact hroot.hOcc 490
  · exact hroot.hOcc 495
  · exact hroot.hOcc 514
  · exact hroot.hOcc 519
  · exact hroot.hOcc 565
  · exact hroot.hOcc 574
  · exact hroot.hOcc 575
  · exact hroot.hOcc 582
  · exact hroot.hOcc 606
  · exact hroot.hOcc 621
  · exact hroot.hOcc 622
  · exact hroot.hOcc 640
  · exact hroot.hOcc 643
  · exact hroot.hOcc 687
  · exact hroot.hOcc 694
  · exact hroot.hOcc 711
  · exact hroot.hOcc 714
  · exact hroot.hOcc 715
  · exact hroot.hOcc 717
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (16 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (11 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (22 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (15 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (48 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_48
  · change (∑ k, (if k = (38 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38

end QiushiMatmul
