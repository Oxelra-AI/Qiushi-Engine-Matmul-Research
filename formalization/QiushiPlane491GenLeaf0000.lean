import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0000Refs : Fin 50 → RowRef 726 49 := ![.occ 82, .occ 83, .occ 94, .occ 103, .occ 105, .occ 107, .occ 115, .occ 119, .occ 165, .occ 230, .occ 231, .occ 237, .occ 257, .occ 305, .occ 324, .occ 326, .occ 335, .occ 351, .occ 358, .occ 365, .occ 381, .occ 392, .occ 414, .occ 419, .occ 431, .occ 432, .occ 532, .occ 545, .occ 549, .occ 552, .occ 559, .occ 563, .occ 584, .occ 666, .occ 671, .occ 716, .sumGe, .nonneg 44, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchLe 29 (0), .branchLe 46 (0), .branchLe 32 (0), .branchLe 38 (0), .branchLe 6 (0), .branchLe 9 (0), .branchLe 4 (0), .branchLe 0 (0), .branchLe 43 (0)]

def plane491GenLeaf0000Mult : Fin 50 → Nat := ![5737, 17937, 30240, 16010, 49810, 39321, 43812, 49346, 14044, 45072, 9682, 23187, 49211, 17492, 6972, 427, 6743, 1533, 22208, 11925, 3071, 9149, 14075, 30399, 27207, 3810, 20773, 5676, 30940, 3350, 28363, 38579, 43409, 8089, 34864, 11866, 140938, 9403, 94208, 51236, 107998, 140938, 118730, 80721, 113731, 140938, 82834, 99656, 93628, 101909]

theorem plane491GenLeaf0000 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_46 : x 46 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_43 : x 43 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0000Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0000Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 82
  · exact hroot.hOcc 83
  · exact hroot.hOcc 94
  · exact hroot.hOcc 103
  · exact hroot.hOcc 105
  · exact hroot.hOcc 107
  · exact hroot.hOcc 115
  · exact hroot.hOcc 119
  · exact hroot.hOcc 165
  · exact hroot.hOcc 230
  · exact hroot.hOcc 231
  · exact hroot.hOcc 237
  · exact hroot.hOcc 257
  · exact hroot.hOcc 305
  · exact hroot.hOcc 324
  · exact hroot.hOcc 326
  · exact hroot.hOcc 335
  · exact hroot.hOcc 351
  · exact hroot.hOcc 358
  · exact hroot.hOcc 365
  · exact hroot.hOcc 381
  · exact hroot.hOcc 392
  · exact hroot.hOcc 414
  · exact hroot.hOcc 419
  · exact hroot.hOcc 431
  · exact hroot.hOcc 432
  · exact hroot.hOcc 532
  · exact hroot.hOcc 545
  · exact hroot.hOcc 549
  · exact hroot.hOcc 552
  · exact hroot.hOcc 559
  · exact hroot.hOcc 563
  · exact hroot.hOcc 584
  · exact hroot.hOcc 666
  · exact hroot.hOcc 671
  · exact hroot.hOcc 716
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (44 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (46 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_46
  · change (∑ k, (if k = (32 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (38 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (6 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (9 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (4 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (0 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (43 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43

end QiushiMatmul
