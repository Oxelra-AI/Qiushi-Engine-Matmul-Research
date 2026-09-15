import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0036Refs : Fin 50 → RowRef 726 49 := ![.occ 81, .occ 94, .occ 109, .occ 112, .occ 116, .occ 157, .occ 158, .occ 197, .occ 199, .occ 237, .occ 255, .occ 258, .occ 260, .occ 287, .occ 292, .occ 318, .occ 319, .occ 328, .occ 335, .occ 348, .occ 351, .occ 364, .occ 395, .occ 400, .occ 422, .occ 430, .occ 464, .occ 495, .occ 504, .occ 513, .occ 533, .occ 581, .occ 584, .occ 585, .occ 603, .occ 628, .occ 631, .occ 651, .occ 707, .occ 718, .occ 721, .sumGe, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchGe 29 (1), .branchLe 43 (0), .branchLe 9 (0), .branchLe 5 (0), .branchGe 44 (1)]

def plane491GenLeaf0036Mult : Fin 50 → Nat := ![374457, 51619, 1038012, 858422, 1045897, 335304, 406752, 341493, 247645, 359148, 296432, 177099, 16031, 23865, 21150, 606040, 78460, 72558, 70313, 445810, 379295, 432474, 305337, 237094, 212759, 697524, 141232, 399053, 209533, 228975, 84363, 127894, 265465, 11685, 134498, 5529, 309968, 168811, 186984, 388823, 13140, 1579993, 1180940, 476448, 1579993, 3520484, 1579993, 1393009, 591153, 4929644]

theorem plane491GenLeaf0036 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_44 : (1 : Int) ≤ x 44)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_43 : x 43 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0036Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0036Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0036Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0036Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 81
  · exact hroot.hOcc 94
  · exact hroot.hOcc 109
  · exact hroot.hOcc 112
  · exact hroot.hOcc 116
  · exact hroot.hOcc 157
  · exact hroot.hOcc 158
  · exact hroot.hOcc 197
  · exact hroot.hOcc 199
  · exact hroot.hOcc 237
  · exact hroot.hOcc 255
  · exact hroot.hOcc 258
  · exact hroot.hOcc 260
  · exact hroot.hOcc 287
  · exact hroot.hOcc 292
  · exact hroot.hOcc 318
  · exact hroot.hOcc 319
  · exact hroot.hOcc 328
  · exact hroot.hOcc 335
  · exact hroot.hOcc 348
  · exact hroot.hOcc 351
  · exact hroot.hOcc 364
  · exact hroot.hOcc 395
  · exact hroot.hOcc 400
  · exact hroot.hOcc 422
  · exact hroot.hOcc 430
  · exact hroot.hOcc 464
  · exact hroot.hOcc 495
  · exact hroot.hOcc 504
  · exact hroot.hOcc 513
  · exact hroot.hOcc 533
  · exact hroot.hOcc 581
  · exact hroot.hOcc 584
  · exact hroot.hOcc 585
  · exact hroot.hOcc 603
  · exact hroot.hOcc 628
  · exact hroot.hOcc 631
  · exact hroot.hOcc 651
  · exact hroot.hOcc 707
  · exact hroot.hOcc 718
  · exact hroot.hOcc 721
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (43 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (9 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (5 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (44 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_44

end QiushiMatmul
