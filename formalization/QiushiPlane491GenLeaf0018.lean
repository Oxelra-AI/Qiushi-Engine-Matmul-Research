import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0018Refs : Fin 50 → RowRef 726 49 := ![.occ 79, .occ 84, .occ 102, .occ 103, .occ 108, .occ 109, .occ 115, .occ 121, .occ 148, .occ 178, .occ 219, .occ 222, .occ 237, .occ 244, .occ 258, .occ 287, .occ 293, .occ 304, .occ 326, .occ 365, .occ 392, .occ 396, .occ 431, .occ 472, .occ 563, .occ 568, .occ 570, .occ 585, .occ 586, .occ 621, .occ 630, .occ 643, .occ 651, .occ 664, .occ 667, .occ 707, .occ 711, .occ 713, .occ 714, .occ 718, .sumGe, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchLe 29 (0), .branchLe 46 (0), .branchLe 32 (0), .branchGe 38 (1), .branchLe 1 (0), .branchGe 10 (1)]

def plane491GenLeaf0018Mult : Fin 50 → Nat := ![1544761, 1235150, 183355, 1607095, 1160235, 1201172, 2813207, 2388851, 498663, 429371, 1514805, 110881, 635116, 263757, 385501, 222323, 1166797, 773314, 423300, 171872, 200074, 2578169, 932864, 236882, 804094, 102147, 939339, 34988, 425073, 347801, 582638, 598049, 334674, 444271, 29975, 23787, 16337, 674870, 1493864, 402261, 4207824, 4191487, 2754009, 1155562, 1750954, 2612285, 1074994, 8117057, 231016, 12968331]

theorem plane491GenLeaf0018 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_46 : x 46 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0018Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0018Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0018Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0018Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 79
  · exact hroot.hOcc 84
  · exact hroot.hOcc 102
  · exact hroot.hOcc 103
  · exact hroot.hOcc 108
  · exact hroot.hOcc 109
  · exact hroot.hOcc 115
  · exact hroot.hOcc 121
  · exact hroot.hOcc 148
  · exact hroot.hOcc 178
  · exact hroot.hOcc 219
  · exact hroot.hOcc 222
  · exact hroot.hOcc 237
  · exact hroot.hOcc 244
  · exact hroot.hOcc 258
  · exact hroot.hOcc 287
  · exact hroot.hOcc 293
  · exact hroot.hOcc 304
  · exact hroot.hOcc 326
  · exact hroot.hOcc 365
  · exact hroot.hOcc 392
  · exact hroot.hOcc 396
  · exact hroot.hOcc 431
  · exact hroot.hOcc 472
  · exact hroot.hOcc 563
  · exact hroot.hOcc 568
  · exact hroot.hOcc 570
  · exact hroot.hOcc 585
  · exact hroot.hOcc 586
  · exact hroot.hOcc 621
  · exact hroot.hOcc 630
  · exact hroot.hOcc 643
  · exact hroot.hOcc 651
  · exact hroot.hOcc 664
  · exact hroot.hOcc 667
  · exact hroot.hOcc 707
  · exact hroot.hOcc 711
  · exact hroot.hOcc 713
  · exact hroot.hOcc 714
  · exact hroot.hOcc 718
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (46 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_46
  · change (∑ k, (if k = (32 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (38 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38
  · change (∑ k, (if k = (1 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (10 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10

end QiushiMatmul
