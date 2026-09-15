import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0028Refs : Fin 50 → RowRef 726 49 := ![.occ 78, .occ 104, .occ 108, .occ 114, .occ 115, .occ 117, .occ 190, .occ 209, .occ 219, .occ 267, .occ 305, .occ 312, .occ 314, .occ 315, .occ 317, .occ 320, .occ 324, .occ 329, .occ 340, .occ 351, .occ 377, .occ 379, .occ 382, .occ 386, .occ 401, .occ 410, .occ 431, .occ 444, .occ 513, .occ 534, .occ 548, .occ 549, .occ 554, .occ 555, .occ 571, .occ 575, .occ 585, .occ 607, .occ 638, .occ 700, .occ 711, .sumGe, .nonneg 5, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchLe 29 (0), .branchGe 46 (1), .branchLe 14 (0), .branchGe 43 (1)]

def plane491GenLeaf0028Mult : Fin 50 → Nat := ![14823, 19434, 131246, 92611, 7851, 104977, 6388, 42604, 8426, 83881, 19223, 32746, 47978, 110697, 5458, 24055, 17482, 44594, 67806, 7803, 30154, 1662, 18744, 42395, 86859, 7928, 42690, 11964, 3863, 7508, 75493, 5547, 10404, 46422, 9410, 16545, 14047, 109703, 36686, 3777, 25544, 203662, 84972, 25285, 198115, 203662, 107393, 743750, 183951, 610284]

theorem plane491GenLeaf0028 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_46 : (1 : Int) ≤ x 46)
    (hLB_43 : (1 : Int) ≤ x 43)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0028Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0028Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0028Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0028Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 78
  · exact hroot.hOcc 104
  · exact hroot.hOcc 108
  · exact hroot.hOcc 114
  · exact hroot.hOcc 115
  · exact hroot.hOcc 117
  · exact hroot.hOcc 190
  · exact hroot.hOcc 209
  · exact hroot.hOcc 219
  · exact hroot.hOcc 267
  · exact hroot.hOcc 305
  · exact hroot.hOcc 312
  · exact hroot.hOcc 314
  · exact hroot.hOcc 315
  · exact hroot.hOcc 317
  · exact hroot.hOcc 320
  · exact hroot.hOcc 324
  · exact hroot.hOcc 329
  · exact hroot.hOcc 340
  · exact hroot.hOcc 351
  · exact hroot.hOcc 377
  · exact hroot.hOcc 379
  · exact hroot.hOcc 382
  · exact hroot.hOcc 386
  · exact hroot.hOcc 401
  · exact hroot.hOcc 410
  · exact hroot.hOcc 431
  · exact hroot.hOcc 444
  · exact hroot.hOcc 513
  · exact hroot.hOcc 534
  · exact hroot.hOcc 548
  · exact hroot.hOcc 549
  · exact hroot.hOcc 554
  · exact hroot.hOcc 555
  · exact hroot.hOcc 571
  · exact hroot.hOcc 575
  · exact hroot.hOcc 585
  · exact hroot.hOcc 607
  · exact hroot.hOcc 638
  · exact hroot.hOcc 700
  · exact hroot.hOcc 711
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (5 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (46 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_46
  · change (∑ k, (if k = (14 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (43 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_43

end QiushiMatmul
