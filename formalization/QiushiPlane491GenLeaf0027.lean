import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0027Refs : Fin 50 → RowRef 726 49 := ![.occ 80, .occ 101, .occ 109, .occ 112, .occ 113, .occ 117, .occ 134, .occ 207, .occ 208, .occ 209, .occ 219, .occ 221, .occ 237, .occ 310, .occ 313, .occ 315, .occ 316, .occ 320, .occ 329, .occ 340, .occ 341, .occ 368, .occ 370, .occ 377, .occ 400, .occ 402, .occ 414, .occ 431, .occ 458, .occ 495, .occ 557, .occ 559, .occ 586, .occ 621, .occ 642, .occ 662, .occ 685, .occ 697, .occ 706, .occ 711, .occ 713, .sumGe, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchLe 29 (0), .branchGe 46 (1), .branchLe 14 (0), .branchLe 43 (0), .branchGe 8 (1)]

def plane491GenLeaf0027Mult : Fin 50 → Nat := ![301545, 60498, 7753, 216170, 166885, 266545, 105367, 244514, 236230, 9729, 84736, 105667, 131611, 69732, 29146, 174978, 46631, 121072, 256569, 147958, 7753, 174237, 19691, 143074, 305036, 50651, 7576, 158908, 113941, 7753, 89167, 45169, 28004, 60498, 207935, 14229, 74674, 98578, 13585, 58610, 9479, 564143, 226982, 204459, 181971, 198977, 2144543, 334211, 384461, 1376679]

theorem plane491GenLeaf0027 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_46 : (1 : Int) ≤ x 46)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_43 : x 43 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0027Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0027Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0027Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0027Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 80
  · exact hroot.hOcc 101
  · exact hroot.hOcc 109
  · exact hroot.hOcc 112
  · exact hroot.hOcc 113
  · exact hroot.hOcc 117
  · exact hroot.hOcc 134
  · exact hroot.hOcc 207
  · exact hroot.hOcc 208
  · exact hroot.hOcc 209
  · exact hroot.hOcc 219
  · exact hroot.hOcc 221
  · exact hroot.hOcc 237
  · exact hroot.hOcc 310
  · exact hroot.hOcc 313
  · exact hroot.hOcc 315
  · exact hroot.hOcc 316
  · exact hroot.hOcc 320
  · exact hroot.hOcc 329
  · exact hroot.hOcc 340
  · exact hroot.hOcc 341
  · exact hroot.hOcc 368
  · exact hroot.hOcc 370
  · exact hroot.hOcc 377
  · exact hroot.hOcc 400
  · exact hroot.hOcc 402
  · exact hroot.hOcc 414
  · exact hroot.hOcc 431
  · exact hroot.hOcc 458
  · exact hroot.hOcc 495
  · exact hroot.hOcc 557
  · exact hroot.hOcc 559
  · exact hroot.hOcc 586
  · exact hroot.hOcc 621
  · exact hroot.hOcc 642
  · exact hroot.hOcc 662
  · exact hroot.hOcc 685
  · exact hroot.hOcc 697
  · exact hroot.hOcc 706
  · exact hroot.hOcc 711
  · exact hroot.hOcc 713
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (46 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_46
  · change (∑ k, (if k = (14 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (43 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (8 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8

end QiushiMatmul
