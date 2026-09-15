import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0011Refs : Fin 50 → RowRef 726 49 := ![.occ 79, .occ 81, .occ 89, .occ 104, .occ 128, .occ 177, .occ 219, .occ 220, .occ 222, .occ 256, .occ 260, .occ 367, .occ 377, .occ 414, .occ 456, .occ 486, .occ 494, .occ 495, .occ 502, .occ 504, .occ 509, .occ 510, .occ 513, .occ 563, .occ 568, .occ 573, .occ 574, .occ 575, .occ 576, .occ 624, .occ 643, .occ 685, .occ 702, .occ 711, .occ 722, .occ 724, .sumGe, .nonneg 34, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchLe 29 (0), .branchLe 46 (0), .branchLe 32 (0), .branchLe 38 (0), .branchGe 6 (1), .branchGe 0 (1), .branchLe 3 (0), .branchLe 47 (0), .branchGe 4 (1)]

def plane491GenLeaf0011Mult : Fin 50 → Nat := ![267363, 175492, 490274, 63343, 182287, 177279, 68786, 94806, 66095, 9448, 210573, 34406, 155776, 11494, 39774, 56556, 36746, 101823, 76999, 47759, 13010, 13010, 141870, 52416, 23524, 76596, 4653, 112123, 104880, 61531, 42962, 38597, 13470, 34550, 6643, 110601, 511216, 58230, 368200, 388799, 357438, 486450, 187574, 363869, 375454, 385412, 875452, 103147, 511216, 1203050]

theorem plane491GenLeaf0011 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hUB_46 : x 46 ≤ (0 : Int))
    (hUB_47 : x 47 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_38 : x 38 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0011Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0011Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0011Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0011Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 79
  · exact hroot.hOcc 81
  · exact hroot.hOcc 89
  · exact hroot.hOcc 104
  · exact hroot.hOcc 128
  · exact hroot.hOcc 177
  · exact hroot.hOcc 219
  · exact hroot.hOcc 220
  · exact hroot.hOcc 222
  · exact hroot.hOcc 256
  · exact hroot.hOcc 260
  · exact hroot.hOcc 367
  · exact hroot.hOcc 377
  · exact hroot.hOcc 414
  · exact hroot.hOcc 456
  · exact hroot.hOcc 486
  · exact hroot.hOcc 494
  · exact hroot.hOcc 495
  · exact hroot.hOcc 502
  · exact hroot.hOcc 504
  · exact hroot.hOcc 509
  · exact hroot.hOcc 510
  · exact hroot.hOcc 513
  · exact hroot.hOcc 563
  · exact hroot.hOcc 568
  · exact hroot.hOcc 573
  · exact hroot.hOcc 574
  · exact hroot.hOcc 575
  · exact hroot.hOcc 576
  · exact hroot.hOcc 624
  · exact hroot.hOcc 643
  · exact hroot.hOcc 685
  · exact hroot.hOcc 702
  · exact hroot.hOcc 711
  · exact hroot.hOcc 722
  · exact hroot.hOcc 724
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (34 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 34
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (46 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_46
  · change (∑ k, (if k = (32 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (38 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (6 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (0 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (3 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (47 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_47
  · change (∑ k, (if k = (4 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4

end QiushiMatmul
