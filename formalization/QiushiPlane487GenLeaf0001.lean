import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0001Refs : Fin 49 → RowRef 668 48 := ![.occ 83, .occ 87, .occ 93, .occ 101, .occ 104, .occ 106, .occ 122, .occ 155, .occ 157, .occ 183, .occ 189, .occ 192, .occ 225, .occ 246, .occ 269, .occ 288, .occ 297, .occ 303, .occ 352, .occ 380, .occ 386, .occ 394, .occ 412, .occ 472, .occ 488, .occ 508, .occ 536, .occ 572, .occ 577, .occ 581, .occ 625, .occ 637, .occ 639, .occ 650, .occ 652, .occ 656, .occ 664, .sumGe, .branchLe 39 (0), .branchLe 23 (0), .branchLe 6 (0), .branchLe 25 (0), .branchLe 12 (0), .branchLe 15 (0), .branchLe 16 (0), .branchLe 38 (0), .branchGe 9 (1), .branchLe 33 (0), .branchLe 19 (0)]

def plane487GenLeaf0001Mult : Fin 49 → Nat := ![391831, 44709, 194128, 202659, 83952, 262140, 100637, 59939, 69227, 167583, 95203, 157020, 230201, 240244, 278919, 4602, 351372, 383186, 70407, 170788, 61450, 100884, 355164, 5125, 129441, 52239, 157102, 45489, 17759, 102788, 134919, 51506, 121913, 88376, 188358, 60042, 238664, 1089538, 757373, 851089, 996037, 1029496, 528304, 798571, 967625, 1028088, 184973, 626618, 576498]

theorem plane487GenLeaf0001 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0001Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0001Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 83
  · exact hroot.hOcc 87
  · exact hroot.hOcc 93
  · exact hroot.hOcc 101
  · exact hroot.hOcc 104
  · exact hroot.hOcc 106
  · exact hroot.hOcc 122
  · exact hroot.hOcc 155
  · exact hroot.hOcc 157
  · exact hroot.hOcc 183
  · exact hroot.hOcc 189
  · exact hroot.hOcc 192
  · exact hroot.hOcc 225
  · exact hroot.hOcc 246
  · exact hroot.hOcc 269
  · exact hroot.hOcc 288
  · exact hroot.hOcc 297
  · exact hroot.hOcc 303
  · exact hroot.hOcc 352
  · exact hroot.hOcc 380
  · exact hroot.hOcc 386
  · exact hroot.hOcc 394
  · exact hroot.hOcc 412
  · exact hroot.hOcc 472
  · exact hroot.hOcc 488
  · exact hroot.hOcc 508
  · exact hroot.hOcc 536
  · exact hroot.hOcc 572
  · exact hroot.hOcc 577
  · exact hroot.hOcc 581
  · exact hroot.hOcc 625
  · exact hroot.hOcc 637
  · exact hroot.hOcc 639
  · exact hroot.hOcc 650
  · exact hroot.hOcc 652
  · exact hroot.hOcc 656
  · exact hroot.hOcc 664
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (6 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (25 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (12 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (15 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (16 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (38 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (9 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9
  · change (∑ k, (if k = (33 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (19 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19

end QiushiMatmul
