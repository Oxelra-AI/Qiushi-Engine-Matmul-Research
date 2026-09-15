import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0089Refs : Fin 50 → RowRef 726 49 := ![.occ 86, .occ 98, .occ 99, .occ 103, .occ 111, .occ 118, .occ 124, .occ 129, .occ 169, .occ 220, .occ 221, .occ 223, .occ 248, .occ 254, .occ 257, .occ 326, .occ 329, .occ 334, .occ 341, .occ 343, .occ 350, .occ 365, .occ 400, .occ 423, .occ 482, .occ 484, .occ 487, .occ 524, .occ 564, .occ 565, .occ 566, .occ 582, .occ 589, .occ 607, .occ 630, .occ 632, .occ 653, .occ 662, .occ 686, .occ 715, .occ 722, .sumGe, .nonneg 37, .branchGe 31 (1), .branchLe 44 (0), .branchGe 11 (1), .branchLe 2 (0), .branchLe 7 (0), .branchLe 39 (0), .branchLe 38 (0)]

def plane491GenLeaf0089Mult : Fin 50 → Nat := ![403608, 290219, 957937, 865084, 265907, 678993, 298350, 43707, 541251, 351197, 67141, 49137, 5520, 34622, 52145, 25556, 405672, 488301, 311963, 166263, 361880, 2834, 192130, 58510, 54283, 237576, 190495, 16091, 75279, 251905, 77202, 52521, 278149, 35638, 162724, 307479, 103711, 413203, 51147, 148677, 104476, 1211411, 205472, 2879860, 1019152, 4093666, 550208, 101798, 1158890, 693732]

theorem plane491GenLeaf0089 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0089Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0089Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0089Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0089Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 86
  · exact hroot.hOcc 98
  · exact hroot.hOcc 99
  · exact hroot.hOcc 103
  · exact hroot.hOcc 111
  · exact hroot.hOcc 118
  · exact hroot.hOcc 124
  · exact hroot.hOcc 129
  · exact hroot.hOcc 169
  · exact hroot.hOcc 220
  · exact hroot.hOcc 221
  · exact hroot.hOcc 223
  · exact hroot.hOcc 248
  · exact hroot.hOcc 254
  · exact hroot.hOcc 257
  · exact hroot.hOcc 326
  · exact hroot.hOcc 329
  · exact hroot.hOcc 334
  · exact hroot.hOcc 341
  · exact hroot.hOcc 343
  · exact hroot.hOcc 350
  · exact hroot.hOcc 365
  · exact hroot.hOcc 400
  · exact hroot.hOcc 423
  · exact hroot.hOcc 482
  · exact hroot.hOcc 484
  · exact hroot.hOcc 487
  · exact hroot.hOcc 524
  · exact hroot.hOcc 564
  · exact hroot.hOcc 565
  · exact hroot.hOcc 566
  · exact hroot.hOcc 582
  · exact hroot.hOcc 589
  · exact hroot.hOcc 607
  · exact hroot.hOcc 630
  · exact hroot.hOcc 632
  · exact hroot.hOcc 653
  · exact hroot.hOcc 662
  · exact hroot.hOcc 686
  · exact hroot.hOcc 715
  · exact hroot.hOcc 722
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (37 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (11 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11
  · change (∑ k, (if k = (2 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (7 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (39 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (38 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38

end QiushiMatmul
