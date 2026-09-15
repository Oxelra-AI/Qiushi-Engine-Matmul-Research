import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0015Refs : Fin 50 → RowRef 726 49 := ![.occ 88, .occ 94, .occ 102, .occ 179, .occ 183, .occ 202, .occ 205, .occ 244, .occ 287, .occ 291, .occ 304, .occ 306, .occ 320, .occ 324, .occ 377, .occ 379, .occ 425, .occ 427, .occ 431, .occ 491, .occ 507, .occ 508, .occ 515, .occ 532, .occ 534, .occ 552, .occ 565, .occ 570, .occ 594, .occ 666, .occ 685, .occ 692, .occ 700, .occ 707, .occ 711, .occ 722, .sumGe, .nonneg 47, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchLe 29 (0), .branchLe 46 (0), .branchLe 32 (0), .branchGe 38 (1), .branchLe 1 (0), .branchLe 10 (0), .branchLe 7 (0), .branchLe 8 (0), .branchGe 12 (1)]

def plane491GenLeaf0015Mult : Fin 50 → Nat := ![25394, 512895, 334236, 327958, 117323, 206232, 17144, 3450, 179339, 39501, 60274, 23650, 10974, 35754, 62441, 53092, 67748, 78557, 135608, 22658, 55729, 3347, 30434, 122975, 78934, 54999, 121845, 257067, 34624, 58909, 59477, 88537, 111569, 116449, 68353, 205511, 688530, 33290, 292821, 688530, 394482, 241238, 307756, 443028, 1545211, 605403, 393492, 512604, 487358, 1263279]

theorem plane491GenLeaf0015 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_46 : x 46 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0015Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0015Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0015Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0015Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 88
  · exact hroot.hOcc 94
  · exact hroot.hOcc 102
  · exact hroot.hOcc 179
  · exact hroot.hOcc 183
  · exact hroot.hOcc 202
  · exact hroot.hOcc 205
  · exact hroot.hOcc 244
  · exact hroot.hOcc 287
  · exact hroot.hOcc 291
  · exact hroot.hOcc 304
  · exact hroot.hOcc 306
  · exact hroot.hOcc 320
  · exact hroot.hOcc 324
  · exact hroot.hOcc 377
  · exact hroot.hOcc 379
  · exact hroot.hOcc 425
  · exact hroot.hOcc 427
  · exact hroot.hOcc 431
  · exact hroot.hOcc 491
  · exact hroot.hOcc 507
  · exact hroot.hOcc 508
  · exact hroot.hOcc 515
  · exact hroot.hOcc 532
  · exact hroot.hOcc 534
  · exact hroot.hOcc 552
  · exact hroot.hOcc 565
  · exact hroot.hOcc 570
  · exact hroot.hOcc 594
  · exact hroot.hOcc 666
  · exact hroot.hOcc 685
  · exact hroot.hOcc 692
  · exact hroot.hOcc 700
  · exact hroot.hOcc 707
  · exact hroot.hOcc 711
  · exact hroot.hOcc 722
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (47 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (46 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_46
  · change (∑ k, (if k = (32 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (38 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38
  · change (∑ k, (if k = (1 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (10 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (7 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (8 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (12 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12

end QiushiMatmul
