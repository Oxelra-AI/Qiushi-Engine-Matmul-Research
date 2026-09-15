import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0043Refs : Fin 50 → RowRef 726 49 := ![.occ 97, .occ 108, .occ 109, .occ 114, .occ 115, .occ 158, .occ 199, .occ 241, .occ 256, .occ 287, .occ 304, .occ 324, .occ 325, .occ 326, .occ 331, .occ 351, .occ 354, .occ 364, .occ 372, .occ 373, .occ 394, .occ 401, .occ 430, .occ 431, .occ 495, .occ 513, .occ 526, .occ 541, .occ 542, .occ 549, .occ 571, .occ 576, .occ 632, .occ 654, .occ 656, .occ 677, .occ 686, .occ 691, .occ 707, .occ 714, .sumGe, .nonneg 46, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchGe 29 (1), .branchGe 43 (1), .branchLe 32 (0), .branchLe 0 (0), .branchLe 21 (0)]

def plane491GenLeaf0043Mult : Fin 50 → Nat := ![543901, 962003, 82625, 587539, 343437, 27704, 216907, 317736, 174239, 31595, 463944, 345844, 560488, 107217, 6484, 73234, 130988, 168523, 108356, 121432, 119448, 652762, 110143, 276025, 172480, 43727, 613959, 83900, 175216, 108733, 538942, 34200, 187235, 363780, 10522, 149111, 231836, 13102, 200917, 176055, 1510656, 119845, 1338176, 1192091, 1239521, 3371088, 3645629, 609444, 1497554, 1476456]

theorem plane491GenLeaf0043 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_43 : (1 : Int) ≤ x 43)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0043Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0043Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0043Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0043Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 97
  · exact hroot.hOcc 108
  · exact hroot.hOcc 109
  · exact hroot.hOcc 114
  · exact hroot.hOcc 115
  · exact hroot.hOcc 158
  · exact hroot.hOcc 199
  · exact hroot.hOcc 241
  · exact hroot.hOcc 256
  · exact hroot.hOcc 287
  · exact hroot.hOcc 304
  · exact hroot.hOcc 324
  · exact hroot.hOcc 325
  · exact hroot.hOcc 326
  · exact hroot.hOcc 331
  · exact hroot.hOcc 351
  · exact hroot.hOcc 354
  · exact hroot.hOcc 364
  · exact hroot.hOcc 372
  · exact hroot.hOcc 373
  · exact hroot.hOcc 394
  · exact hroot.hOcc 401
  · exact hroot.hOcc 430
  · exact hroot.hOcc 431
  · exact hroot.hOcc 495
  · exact hroot.hOcc 513
  · exact hroot.hOcc 526
  · exact hroot.hOcc 541
  · exact hroot.hOcc 542
  · exact hroot.hOcc 549
  · exact hroot.hOcc 571
  · exact hroot.hOcc 576
  · exact hroot.hOcc 632
  · exact hroot.hOcc 654
  · exact hroot.hOcc 656
  · exact hroot.hOcc 677
  · exact hroot.hOcc 686
  · exact hroot.hOcc 691
  · exact hroot.hOcc 707
  · exact hroot.hOcc 714
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (46 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (43 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_43
  · change (∑ k, (if k = (32 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (0 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (21 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21

end QiushiMatmul
