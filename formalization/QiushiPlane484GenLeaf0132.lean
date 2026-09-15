import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0132Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 127, .occ 132, .occ 139, .occ 148, .occ 167, .occ 169, .occ 283, .occ 456, .occ 582, .occ 625, .occ 929, .occ 1111, .occ 1148, .occ 1172, .occ 1215, .occ 1273, .occ 1290, .occ 1341, .occ 1352, .occ 1372, .occ 1381, .occ 1396, .occ 1443, .occ 1471, .occ 1519, .occ 1545, .occ 1603, .occ 1623, .occ 1651, .occ 1660, .sumGe, .nonneg 10, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 39 (0), .branchGe 32 (1), .branchLe 37 (0), .branchLe 3 (0), .branchGe 12 (1), .branchLe 25 (0)]

def plane484GenLeaf0132Mult : Fin 44 → Nat := ![6232, 1225, 7986, 909, 9319, 254, 6422, 7146, 16481, 6648, 2952, 422, 748, 717, 10745, 1847, 2147, 2019, 648, 330, 4057, 2714, 8600, 3170, 6487, 4184, 2598, 348, 65, 6359, 62, 25438, 848, 19017, 25438, 25029, 24725, 15485, 25438, 57852, 25090, 18292, 24800, 25373]

theorem plane484GenLeaf0132 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0132Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0132Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0132Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0132Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 127
  · exact hroot.hOcc 132
  · exact hroot.hOcc 139
  · exact hroot.hOcc 148
  · exact hroot.hOcc 167
  · exact hroot.hOcc 169
  · exact hroot.hOcc 283
  · exact hroot.hOcc 456
  · exact hroot.hOcc 582
  · exact hroot.hOcc 625
  · exact hroot.hOcc 929
  · exact hroot.hOcc 1111
  · exact hroot.hOcc 1148
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1273
  · exact hroot.hOcc 1290
  · exact hroot.hOcc 1341
  · exact hroot.hOcc 1352
  · exact hroot.hOcc 1372
  · exact hroot.hOcc 1381
  · exact hroot.hOcc 1396
  · exact hroot.hOcc 1443
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1519
  · exact hroot.hOcc 1545
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1623
  · exact hroot.hOcc 1651
  · exact hroot.hOcc 1660
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (32 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32
  · change (∑ k, (if k = (37 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (12 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25

end QiushiMatmul
