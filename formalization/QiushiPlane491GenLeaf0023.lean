import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0023Refs : Fin 50 → RowRef 726 49 := ![.occ 80, .occ 97, .occ 99, .occ 101, .occ 109, .occ 165, .occ 192, .occ 242, .occ 243, .occ 257, .occ 263, .occ 269, .occ 287, .occ 320, .occ 351, .occ 365, .occ 389, .occ 409, .occ 410, .occ 423, .occ 460, .occ 486, .occ 494, .occ 498, .occ 509, .occ 552, .occ 554, .occ 570, .occ 579, .occ 584, .occ 590, .occ 611, .occ 621, .occ 643, .occ 683, .occ 690, .occ 700, .occ 711, .sumGe, .nonneg 34, .nonneg 36, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchLe 29 (0), .branchLe 46 (0), .branchGe 32 (1), .branchGe 28 (1), .branchLe 22 (0), .branchLe 7 (0)]

def plane491GenLeaf0023Mult : Fin 50 → Nat := ![5974, 4543, 86833, 86833, 2277, 68657, 4344, 1145, 27228, 35462, 19600, 28724, 15578, 22235, 51709, 21937, 3736, 31018, 13718, 51705, 33326, 7093, 2550, 14424, 2395, 35979, 1257, 16424, 7392, 46490, 295, 22889, 1204, 18819, 12904, 16238, 55014, 4993, 141847, 5999, 23812, 49356, 141847, 63313, 141847, 81840, 413295, 271550, 74546, 139297]

theorem plane491GenLeaf0023 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hUB_46 : x 46 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0023Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0023Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0023Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0023Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 80
  · exact hroot.hOcc 97
  · exact hroot.hOcc 99
  · exact hroot.hOcc 101
  · exact hroot.hOcc 109
  · exact hroot.hOcc 165
  · exact hroot.hOcc 192
  · exact hroot.hOcc 242
  · exact hroot.hOcc 243
  · exact hroot.hOcc 257
  · exact hroot.hOcc 263
  · exact hroot.hOcc 269
  · exact hroot.hOcc 287
  · exact hroot.hOcc 320
  · exact hroot.hOcc 351
  · exact hroot.hOcc 365
  · exact hroot.hOcc 389
  · exact hroot.hOcc 409
  · exact hroot.hOcc 410
  · exact hroot.hOcc 423
  · exact hroot.hOcc 460
  · exact hroot.hOcc 486
  · exact hroot.hOcc 494
  · exact hroot.hOcc 498
  · exact hroot.hOcc 509
  · exact hroot.hOcc 552
  · exact hroot.hOcc 554
  · exact hroot.hOcc 570
  · exact hroot.hOcc 579
  · exact hroot.hOcc 584
  · exact hroot.hOcc 590
  · exact hroot.hOcc 611
  · exact hroot.hOcc 621
  · exact hroot.hOcc 643
  · exact hroot.hOcc 683
  · exact hroot.hOcc 690
  · exact hroot.hOcc 700
  · exact hroot.hOcc 711
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (34 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 34
  · change (∑ k, (if k = (36 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (46 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_46
  · change (∑ k, (if k = (32 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32
  · change (∑ k, (if k = (28 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (22 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (7 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7

end QiushiMatmul
