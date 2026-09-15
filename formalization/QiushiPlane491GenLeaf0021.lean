import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0021Refs : Fin 50 → RowRef 726 49 := ![.occ 80, .occ 85, .occ 99, .occ 101, .occ 111, .occ 140, .occ 172, .occ 173, .occ 174, .occ 231, .occ 243, .occ 255, .occ 257, .occ 265, .occ 292, .occ 294, .occ 332, .occ 365, .occ 367, .occ 370, .occ 385, .occ 389, .occ 402, .occ 406, .occ 423, .occ 490, .occ 492, .occ 517, .occ 534, .occ 554, .occ 573, .occ 585, .occ 647, .occ 681, .occ 683, .occ 695, .occ 707, .occ 724, .sumGe, .nonneg 4, .nonneg 13, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchLe 29 (0), .branchLe 46 (0), .branchGe 32 (1), .branchLe 28 (0), .branchLe 22 (0), .branchGe 3 (1)]

def plane491GenLeaf0021Mult : Fin 50 → Nat := ![65503, 22913, 137935, 40099, 155456, 17747, 25975, 40675, 40864, 4413, 49396, 65878, 33247, 22928, 108054, 45396, 26427, 32945, 4891, 19913, 37933, 83250, 80371, 88345, 4275, 2254, 74514, 51521, 1683, 30990, 30209, 36680, 23542, 1344, 8294, 3635, 4413, 19178, 190386, 12847, 44015, 126296, 118881, 63749, 105602, 20186, 714612, 190386, 158833, 553470]

theorem plane491GenLeaf0021 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hUB_46 : x 46 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0021Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0021Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0021Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0021Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 80
  · exact hroot.hOcc 85
  · exact hroot.hOcc 99
  · exact hroot.hOcc 101
  · exact hroot.hOcc 111
  · exact hroot.hOcc 140
  · exact hroot.hOcc 172
  · exact hroot.hOcc 173
  · exact hroot.hOcc 174
  · exact hroot.hOcc 231
  · exact hroot.hOcc 243
  · exact hroot.hOcc 255
  · exact hroot.hOcc 257
  · exact hroot.hOcc 265
  · exact hroot.hOcc 292
  · exact hroot.hOcc 294
  · exact hroot.hOcc 332
  · exact hroot.hOcc 365
  · exact hroot.hOcc 367
  · exact hroot.hOcc 370
  · exact hroot.hOcc 385
  · exact hroot.hOcc 389
  · exact hroot.hOcc 402
  · exact hroot.hOcc 406
  · exact hroot.hOcc 423
  · exact hroot.hOcc 490
  · exact hroot.hOcc 492
  · exact hroot.hOcc 517
  · exact hroot.hOcc 534
  · exact hroot.hOcc 554
  · exact hroot.hOcc 573
  · exact hroot.hOcc 585
  · exact hroot.hOcc 647
  · exact hroot.hOcc 681
  · exact hroot.hOcc 683
  · exact hroot.hOcc 695
  · exact hroot.hOcc 707
  · exact hroot.hOcc 724
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (4 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (13 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (46 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_46
  · change (∑ k, (if k = (32 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32
  · change (∑ k, (if k = (28 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (22 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (3 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3

end QiushiMatmul
