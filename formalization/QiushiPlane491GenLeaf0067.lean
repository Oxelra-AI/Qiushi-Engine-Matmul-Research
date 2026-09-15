import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0067Refs : Fin 49 → RowRef 726 49 := ![.occ 83, .occ 89, .occ 96, .occ 115, .occ 136, .occ 137, .occ 223, .occ 248, .occ 257, .occ 278, .occ 287, .occ 306, .occ 318, .occ 326, .occ 329, .occ 331, .occ 332, .occ 355, .occ 365, .occ 367, .occ 372, .occ 400, .occ 414, .occ 419, .occ 420, .occ 429, .occ 454, .occ 478, .occ 494, .occ 495, .occ 510, .occ 524, .occ 525, .occ 549, .occ 570, .occ 578, .occ 585, .occ 599, .occ 602, .occ 605, .occ 714, .occ 721, .occ 723, .sumGe, .branchLe 31 (0), .branchGe 16 (1), .branchLe 20 (0), .branchLe 27 (0), .branchLe 9 (0)]

def plane491GenLeaf0067Mult : Fin 49 → Nat := ![20977081, 876513, 30460615, 5085940, 18249872, 4787585, 10393498, 12397587, 8574493, 1193216, 4193427, 2290160, 8022636, 2440101, 6775316, 10361636, 19128658, 289432, 4026620, 7713360, 2013310, 15549084, 6463639, 11693294, 3450078, 22096040, 15811707, 865550, 1874067, 10698, 7460392, 8621835, 3224929, 3929633, 1873344, 8108336, 2289437, 343029, 1097347, 10639756, 69983, 12721779, 2359420, 49459777, 40024911, 198861675, 41962186, 36811322, 38653267]

theorem plane491GenLeaf0067 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0067Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0067Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0067Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0067Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 83
  · exact hroot.hOcc 89
  · exact hroot.hOcc 96
  · exact hroot.hOcc 115
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 223
  · exact hroot.hOcc 248
  · exact hroot.hOcc 257
  · exact hroot.hOcc 278
  · exact hroot.hOcc 287
  · exact hroot.hOcc 306
  · exact hroot.hOcc 318
  · exact hroot.hOcc 326
  · exact hroot.hOcc 329
  · exact hroot.hOcc 331
  · exact hroot.hOcc 332
  · exact hroot.hOcc 355
  · exact hroot.hOcc 365
  · exact hroot.hOcc 367
  · exact hroot.hOcc 372
  · exact hroot.hOcc 400
  · exact hroot.hOcc 414
  · exact hroot.hOcc 419
  · exact hroot.hOcc 420
  · exact hroot.hOcc 429
  · exact hroot.hOcc 454
  · exact hroot.hOcc 478
  · exact hroot.hOcc 494
  · exact hroot.hOcc 495
  · exact hroot.hOcc 510
  · exact hroot.hOcc 524
  · exact hroot.hOcc 525
  · exact hroot.hOcc 549
  · exact hroot.hOcc 570
  · exact hroot.hOcc 578
  · exact hroot.hOcc 585
  · exact hroot.hOcc 599
  · exact hroot.hOcc 602
  · exact hroot.hOcc 605
  · exact hroot.hOcc 714
  · exact hroot.hOcc 721
  · exact hroot.hOcc 723
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (20 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (9 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9

end QiushiMatmul
