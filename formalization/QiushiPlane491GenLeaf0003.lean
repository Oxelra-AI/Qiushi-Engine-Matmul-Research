import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0003Refs : Fin 50 → RowRef 726 49 := ![.occ 89, .occ 104, .occ 120, .occ 124, .occ 199, .occ 220, .occ 222, .occ 243, .occ 244, .occ 256, .occ 257, .occ 260, .occ 267, .occ 287, .occ 292, .occ 326, .occ 331, .occ 332, .occ 368, .occ 370, .occ 373, .occ 408, .occ 414, .occ 452, .occ 494, .occ 495, .occ 532, .occ 541, .occ 543, .occ 559, .occ 563, .occ 575, .occ 576, .occ 602, .occ 604, .occ 624, .occ 628, .sumGe, .nonneg 5, .nonneg 32, .nonneg 34, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchLe 29 (0), .branchLe 46 (0), .branchLe 38 (0), .branchLe 6 (0), .branchLe 9 (0), .branchGe 4 (1)]

def plane491GenLeaf0003Mult : Fin 50 → Nat := ![233407, 185575, 18342, 50272, 15029, 48339, 97668, 130504, 12170, 13111, 231090, 761, 11861, 10740, 218946, 76388, 54042, 9815, 27871, 89770, 137174, 17569, 22967, 67812, 49982, 60371, 61056, 56892, 19349, 8809, 20680, 170883, 78766, 18315, 57042, 60741, 3752, 413685, 7426, 23411, 150547, 353314, 205071, 328922, 409933, 304566, 401515, 413685, 182061, 1116465]

theorem plane491GenLeaf0003 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_46 : x 46 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_38 : x 38 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0003Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0003Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0003Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0003Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 89
  · exact hroot.hOcc 104
  · exact hroot.hOcc 120
  · exact hroot.hOcc 124
  · exact hroot.hOcc 199
  · exact hroot.hOcc 220
  · exact hroot.hOcc 222
  · exact hroot.hOcc 243
  · exact hroot.hOcc 244
  · exact hroot.hOcc 256
  · exact hroot.hOcc 257
  · exact hroot.hOcc 260
  · exact hroot.hOcc 267
  · exact hroot.hOcc 287
  · exact hroot.hOcc 292
  · exact hroot.hOcc 326
  · exact hroot.hOcc 331
  · exact hroot.hOcc 332
  · exact hroot.hOcc 368
  · exact hroot.hOcc 370
  · exact hroot.hOcc 373
  · exact hroot.hOcc 408
  · exact hroot.hOcc 414
  · exact hroot.hOcc 452
  · exact hroot.hOcc 494
  · exact hroot.hOcc 495
  · exact hroot.hOcc 532
  · exact hroot.hOcc 541
  · exact hroot.hOcc 543
  · exact hroot.hOcc 559
  · exact hroot.hOcc 563
  · exact hroot.hOcc 575
  · exact hroot.hOcc 576
  · exact hroot.hOcc 602
  · exact hroot.hOcc 604
  · exact hroot.hOcc 624
  · exact hroot.hOcc 628
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (5 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (32 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (34 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 34
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (46 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_46
  · change (∑ k, (if k = (38 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (6 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (9 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (4 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4

end QiushiMatmul
