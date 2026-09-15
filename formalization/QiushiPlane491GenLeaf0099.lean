import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0099Refs : Fin 50 → RowRef 726 49 := ![.occ 98, .occ 109, .occ 112, .occ 113, .occ 123, .occ 170, .occ 171, .occ 196, .occ 198, .occ 214, .occ 219, .occ 230, .occ 243, .occ 258, .occ 287, .occ 305, .occ 318, .occ 319, .occ 323, .occ 329, .occ 331, .occ 351, .occ 359, .occ 363, .occ 365, .occ 382, .occ 394, .occ 396, .occ 400, .occ 402, .occ 404, .occ 430, .occ 484, .occ 489, .occ 495, .occ 523, .occ 531, .occ 565, .occ 566, .occ 664, .occ 722, .sumGe, .branchGe 31 (1), .branchGe 44 (1), .branchLe 6 (0), .branchLe 39 (0), .branchGe 28 (1), .branchLe 36 (0), .branchLe 15 (0), .branchLe 47 (0)]

def plane491GenLeaf0099Mult : Fin 50 → Nat := ![17952, 7443, 7397, 3023, 701, 5054, 5571, 3857, 8664, 6481, 3937, 3016, 934, 11817, 2417, 9400, 2980, 324, 3963, 4522, 1510, 1327, 8800, 1539, 9962, 4869, 1246, 4837, 12395, 2167, 5572, 7258, 6842, 3089, 8699, 841, 9429, 2210, 8423, 7849, 12343, 36574, 69287, 62565, 36574, 27875, 22579, 10424, 24935, 25635]

theorem plane491GenLeaf0099 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_44 : (1 : Int) ≤ x 44)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_47 : x 47 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0099Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0099Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0099Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0099Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 98
  · exact hroot.hOcc 109
  · exact hroot.hOcc 112
  · exact hroot.hOcc 113
  · exact hroot.hOcc 123
  · exact hroot.hOcc 170
  · exact hroot.hOcc 171
  · exact hroot.hOcc 196
  · exact hroot.hOcc 198
  · exact hroot.hOcc 214
  · exact hroot.hOcc 219
  · exact hroot.hOcc 230
  · exact hroot.hOcc 243
  · exact hroot.hOcc 258
  · exact hroot.hOcc 287
  · exact hroot.hOcc 305
  · exact hroot.hOcc 318
  · exact hroot.hOcc 319
  · exact hroot.hOcc 323
  · exact hroot.hOcc 329
  · exact hroot.hOcc 331
  · exact hroot.hOcc 351
  · exact hroot.hOcc 359
  · exact hroot.hOcc 363
  · exact hroot.hOcc 365
  · exact hroot.hOcc 382
  · exact hroot.hOcc 394
  · exact hroot.hOcc 396
  · exact hroot.hOcc 400
  · exact hroot.hOcc 402
  · exact hroot.hOcc 404
  · exact hroot.hOcc 430
  · exact hroot.hOcc 484
  · exact hroot.hOcc 489
  · exact hroot.hOcc 495
  · exact hroot.hOcc 523
  · exact hroot.hOcc 531
  · exact hroot.hOcc 565
  · exact hroot.hOcc 566
  · exact hroot.hOcc 664
  · exact hroot.hOcc 722
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_44
  · change (∑ k, (if k = (6 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (39 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (28 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (36 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (15 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (47 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_47

end QiushiMatmul
