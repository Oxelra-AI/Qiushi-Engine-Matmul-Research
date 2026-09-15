import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0101Refs : Fin 44 → RowRef 713 43 := ![.occ 85, .occ 89, .occ 95, .occ 107, .occ 108, .occ 109, .occ 111, .occ 120, .occ 159, .occ 170, .occ 188, .occ 216, .occ 221, .occ 225, .occ 248, .occ 323, .occ 326, .occ 337, .occ 349, .occ 362, .occ 375, .occ 467, .occ 480, .occ 488, .occ 522, .occ 533, .occ 582, .occ 608, .occ 655, .occ 666, .occ 671, .occ 691, .occ 697, .occ 701, .occ 712, .sumGe, .nonneg 35, .branchGe 29 (1), .branchGe 18 (1), .branchLe 14 (0), .branchLe 20 (0), .branchLe 15 (0), .branchLe 12 (0), .branchLe 33 (0)]

def plane490GenLeaf0101Mult : Fin 44 → Nat := ![281, 468, 109, 242, 5207, 1721, 131, 492, 4119, 547, 688, 448, 422, 2417, 2451, 1717, 482, 382, 1520, 1353, 11, 109, 799, 997, 1233, 930, 1586, 16, 577, 1233, 1763, 611, 194, 1039, 2421, 6410, 381, 21576, 11352, 3059, 5371, 5611, 6410, 6410]

theorem plane490GenLeaf0101 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0101Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0101Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0101Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0101Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 85
  · exact hroot.hOcc 89
  · exact hroot.hOcc 95
  · exact hroot.hOcc 107
  · exact hroot.hOcc 108
  · exact hroot.hOcc 109
  · exact hroot.hOcc 111
  · exact hroot.hOcc 120
  · exact hroot.hOcc 159
  · exact hroot.hOcc 170
  · exact hroot.hOcc 188
  · exact hroot.hOcc 216
  · exact hroot.hOcc 221
  · exact hroot.hOcc 225
  · exact hroot.hOcc 248
  · exact hroot.hOcc 323
  · exact hroot.hOcc 326
  · exact hroot.hOcc 337
  · exact hroot.hOcc 349
  · exact hroot.hOcc 362
  · exact hroot.hOcc 375
  · exact hroot.hOcc 467
  · exact hroot.hOcc 480
  · exact hroot.hOcc 488
  · exact hroot.hOcc 522
  · exact hroot.hOcc 533
  · exact hroot.hOcc 582
  · exact hroot.hOcc 608
  · exact hroot.hOcc 655
  · exact hroot.hOcc 666
  · exact hroot.hOcc 671
  · exact hroot.hOcc 691
  · exact hroot.hOcc 697
  · exact hroot.hOcc 701
  · exact hroot.hOcc 712
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 35
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (12 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (33 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33

end QiushiMatmul
