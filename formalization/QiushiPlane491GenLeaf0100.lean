import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0100Refs : Fin 50 → RowRef 726 49 := ![.occ 98, .occ 112, .occ 122, .occ 237, .occ 241, .occ 258, .occ 275, .occ 284, .occ 287, .occ 305, .occ 318, .occ 323, .occ 329, .occ 332, .occ 338, .occ 339, .occ 340, .occ 359, .occ 364, .occ 365, .occ 368, .occ 384, .occ 386, .occ 393, .occ 400, .occ 424, .occ 425, .occ 430, .occ 431, .occ 484, .occ 495, .occ 531, .occ 541, .occ 561, .occ 582, .occ 625, .occ 640, .occ 661, .occ 686, .occ 722, .sumGe, .nonneg 37, .branchGe 31 (1), .branchGe 44 (1), .branchLe 6 (0), .branchLe 39 (0), .branchGe 28 (1), .branchLe 36 (0), .branchLe 15 (0), .branchGe 47 (1)]

def plane491GenLeaf0100Mult : Fin 50 → Nat := ![59847, 48440, 74291, 27120, 34487, 2268, 31568, 16008, 13083, 48532, 23272, 18339, 8506, 36475, 24684, 15664, 63796, 39695, 16016, 33077, 23441, 13813, 33682, 6374, 10902, 32498, 52788, 22994, 7753, 32627, 25197, 76891, 2333, 37227, 2600, 18339, 26388, 2266, 25260, 22209, 158847, 65333, 262624, 200269, 132459, 104033, 239475, 28868, 55568, 367296]

theorem plane491GenLeaf0100 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_44 : (1 : Int) ≤ x 44)
    (hLB_47 : (1 : Int) ≤ x 47)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0100Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0100Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0100Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0100Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 98
  · exact hroot.hOcc 112
  · exact hroot.hOcc 122
  · exact hroot.hOcc 237
  · exact hroot.hOcc 241
  · exact hroot.hOcc 258
  · exact hroot.hOcc 275
  · exact hroot.hOcc 284
  · exact hroot.hOcc 287
  · exact hroot.hOcc 305
  · exact hroot.hOcc 318
  · exact hroot.hOcc 323
  · exact hroot.hOcc 329
  · exact hroot.hOcc 332
  · exact hroot.hOcc 338
  · exact hroot.hOcc 339
  · exact hroot.hOcc 340
  · exact hroot.hOcc 359
  · exact hroot.hOcc 364
  · exact hroot.hOcc 365
  · exact hroot.hOcc 368
  · exact hroot.hOcc 384
  · exact hroot.hOcc 386
  · exact hroot.hOcc 393
  · exact hroot.hOcc 400
  · exact hroot.hOcc 424
  · exact hroot.hOcc 425
  · exact hroot.hOcc 430
  · exact hroot.hOcc 431
  · exact hroot.hOcc 484
  · exact hroot.hOcc 495
  · exact hroot.hOcc 531
  · exact hroot.hOcc 541
  · exact hroot.hOcc 561
  · exact hroot.hOcc 582
  · exact hroot.hOcc 625
  · exact hroot.hOcc 640
  · exact hroot.hOcc 661
  · exact hroot.hOcc 686
  · exact hroot.hOcc 722
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (37 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_44
  · change (∑ k, (if k = (6 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (39 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (28 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (36 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (15 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (47 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_47

end QiushiMatmul
