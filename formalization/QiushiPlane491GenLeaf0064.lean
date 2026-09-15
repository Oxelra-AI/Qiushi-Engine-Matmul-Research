import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0064Refs : Fin 50 → RowRef 726 49 := ![.occ 97, .occ 103, .occ 106, .occ 112, .occ 152, .occ 155, .occ 196, .occ 200, .occ 219, .occ 237, .occ 284, .occ 299, .occ 319, .occ 326, .occ 329, .occ 338, .occ 340, .occ 362, .occ 363, .occ 368, .occ 370, .occ 425, .occ 430, .occ 489, .occ 495, .occ 541, .occ 563, .occ 575, .occ 576, .occ 583, .occ 586, .occ 620, .occ 644, .occ 653, .occ 661, .occ 663, .occ 691, .occ 722, .occ 724, .sumGe, .nonneg 19, .nonneg 32, .nonneg 33, .branchLe 31 (0), .branchLe 16 (0), .branchGe 27 (1), .branchGe 11 (1), .branchGe 44 (1), .branchLe 6 (0), .branchLe 3 (0)]

def plane491GenLeaf0064Mult : Fin 50 → Nat := ![213348, 717134, 669769, 202151, 382598, 89968, 105430, 201091, 166150, 240346, 535662, 721519, 274525, 83865, 240148, 229304, 421283, 96715, 660192, 140653, 39464, 185152, 148492, 384172, 42073, 362096, 202619, 103614, 132748, 48856, 89824, 194033, 185152, 7058, 401214, 144582, 163277, 133099, 48380, 1336515, 186486, 730197, 277711, 921195, 699894, 3231580, 2443254, 2633303, 1329457, 1064736]

theorem plane491GenLeaf0064 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_44 : (1 : Int) ≤ x 44)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0064Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0064Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0064Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0064Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 97
  · exact hroot.hOcc 103
  · exact hroot.hOcc 106
  · exact hroot.hOcc 112
  · exact hroot.hOcc 152
  · exact hroot.hOcc 155
  · exact hroot.hOcc 196
  · exact hroot.hOcc 200
  · exact hroot.hOcc 219
  · exact hroot.hOcc 237
  · exact hroot.hOcc 284
  · exact hroot.hOcc 299
  · exact hroot.hOcc 319
  · exact hroot.hOcc 326
  · exact hroot.hOcc 329
  · exact hroot.hOcc 338
  · exact hroot.hOcc 340
  · exact hroot.hOcc 362
  · exact hroot.hOcc 363
  · exact hroot.hOcc 368
  · exact hroot.hOcc 370
  · exact hroot.hOcc 425
  · exact hroot.hOcc 430
  · exact hroot.hOcc 489
  · exact hroot.hOcc 495
  · exact hroot.hOcc 541
  · exact hroot.hOcc 563
  · exact hroot.hOcc 575
  · exact hroot.hOcc 576
  · exact hroot.hOcc 583
  · exact hroot.hOcc 586
  · exact hroot.hOcc 620
  · exact hroot.hOcc 644
  · exact hroot.hOcc 653
  · exact hroot.hOcc 661
  · exact hroot.hOcc 663
  · exact hroot.hOcc 691
  · exact hroot.hOcc 722
  · exact hroot.hOcc 724
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (19 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (32 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (33 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (11 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11
  · change (∑ k, (if k = (44 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_44
  · change (∑ k, (if k = (6 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (3 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3

end QiushiMatmul
