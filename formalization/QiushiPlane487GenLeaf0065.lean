import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0065Refs : Fin 49 → RowRef 668 48 := ![.occ 83, .occ 86, .occ 100, .occ 113, .occ 160, .occ 161, .occ 165, .occ 211, .occ 223, .occ 224, .occ 225, .occ 227, .occ 230, .occ 235, .occ 260, .occ 288, .occ 308, .occ 315, .occ 343, .occ 373, .occ 383, .occ 401, .occ 402, .occ 414, .occ 425, .occ 453, .occ 460, .occ 463, .occ 468, .occ 470, .occ 479, .occ 509, .occ 521, .occ 559, .occ 572, .occ 594, .occ 639, .occ 644, .occ 650, .sumGe, .nonneg 23, .branchGe 39 (1), .branchLe 7 (0), .branchLe 28 (0), .branchLe 40 (0), .branchLe 29 (0), .branchGe 19 (1), .branchLe 17 (0), .branchGe 4 (1)]

def plane487GenLeaf0065Mult : Fin 49 → Nat := ![35938, 23456, 63577, 11279, 82725, 265585, 22087, 166, 72129, 79617, 7488, 316238, 41549, 1047, 72469, 199904, 38872, 129687, 76017, 106908, 117045, 63847, 84470, 36918, 161571, 5538, 80620, 31172, 62582, 61182, 2247, 37274, 96063, 5662, 71563, 201605, 114143, 37104, 34231, 467190, 57350, 606394, 59740, 371127, 464943, 159910, 1528877, 301873, 1135382]

theorem plane487GenLeaf0065 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0065Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0065Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0065Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0065Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 83
  · exact hroot.hOcc 86
  · exact hroot.hOcc 100
  · exact hroot.hOcc 113
  · exact hroot.hOcc 160
  · exact hroot.hOcc 161
  · exact hroot.hOcc 165
  · exact hroot.hOcc 211
  · exact hroot.hOcc 223
  · exact hroot.hOcc 224
  · exact hroot.hOcc 225
  · exact hroot.hOcc 227
  · exact hroot.hOcc 230
  · exact hroot.hOcc 235
  · exact hroot.hOcc 260
  · exact hroot.hOcc 288
  · exact hroot.hOcc 308
  · exact hroot.hOcc 315
  · exact hroot.hOcc 343
  · exact hroot.hOcc 373
  · exact hroot.hOcc 383
  · exact hroot.hOcc 401
  · exact hroot.hOcc 402
  · exact hroot.hOcc 414
  · exact hroot.hOcc 425
  · exact hroot.hOcc 453
  · exact hroot.hOcc 460
  · exact hroot.hOcc 463
  · exact hroot.hOcc 468
  · exact hroot.hOcc 470
  · exact hroot.hOcc 479
  · exact hroot.hOcc 509
  · exact hroot.hOcc 521
  · exact hroot.hOcc 559
  · exact hroot.hOcc 572
  · exact hroot.hOcc 594
  · exact hroot.hOcc 639
  · exact hroot.hOcc 644
  · exact hroot.hOcc 650
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (23 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (39 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (7 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (28 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (40 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (29 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (19 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (17 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (4 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4

end QiushiMatmul
