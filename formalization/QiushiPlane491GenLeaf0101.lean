import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0101Refs : Fin 50 → RowRef 726 49 := ![.occ 88, .occ 97, .occ 98, .occ 100, .occ 112, .occ 237, .occ 257, .occ 275, .occ 305, .occ 317, .occ 318, .occ 320, .occ 323, .occ 331, .occ 350, .occ 359, .occ 363, .occ 396, .occ 400, .occ 404, .occ 425, .occ 484, .occ 495, .occ 529, .occ 531, .occ 547, .occ 565, .occ 566, .occ 576, .occ 584, .occ 586, .occ 603, .occ 640, .occ 643, .occ 662, .occ 671, .occ 688, .occ 705, .sumGe, .nonneg 33, .nonneg 37, .branchGe 31 (1), .branchGe 44 (1), .branchLe 6 (0), .branchLe 39 (0), .branchGe 28 (1), .branchLe 36 (0), .branchGe 15 (1), .branchLe 9 (0), .branchLe 29 (0)]

def plane491GenLeaf0101Mult : Fin 50 → Nat := ![50908, 3148, 106074, 66407, 144136, 21327, 315, 17142, 34951, 22064, 51375, 784, 43071, 8975, 19455, 77237, 20588, 22333, 33840, 94313, 34584, 35653, 35134, 597, 77664, 16606, 26737, 71686, 9347, 11467, 18603, 25406, 3300, 20601, 36716, 35582, 6346, 9058, 189057, 25836, 36369, 522717, 345595, 176699, 153923, 264973, 33915, 61399, 111393, 155217]

theorem plane491GenLeaf0101 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_44 : (1 : Int) ≤ x 44)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0101Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0101Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0101Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0101Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 88
  · exact hroot.hOcc 97
  · exact hroot.hOcc 98
  · exact hroot.hOcc 100
  · exact hroot.hOcc 112
  · exact hroot.hOcc 237
  · exact hroot.hOcc 257
  · exact hroot.hOcc 275
  · exact hroot.hOcc 305
  · exact hroot.hOcc 317
  · exact hroot.hOcc 318
  · exact hroot.hOcc 320
  · exact hroot.hOcc 323
  · exact hroot.hOcc 331
  · exact hroot.hOcc 350
  · exact hroot.hOcc 359
  · exact hroot.hOcc 363
  · exact hroot.hOcc 396
  · exact hroot.hOcc 400
  · exact hroot.hOcc 404
  · exact hroot.hOcc 425
  · exact hroot.hOcc 484
  · exact hroot.hOcc 495
  · exact hroot.hOcc 529
  · exact hroot.hOcc 531
  · exact hroot.hOcc 547
  · exact hroot.hOcc 565
  · exact hroot.hOcc 566
  · exact hroot.hOcc 576
  · exact hroot.hOcc 584
  · exact hroot.hOcc 586
  · exact hroot.hOcc 603
  · exact hroot.hOcc 640
  · exact hroot.hOcc 643
  · exact hroot.hOcc 662
  · exact hroot.hOcc 671
  · exact hroot.hOcc 688
  · exact hroot.hOcc 705
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (33 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (37 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_44
  · change (∑ k, (if k = (6 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (39 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (28 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (36 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (15 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (9 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (29 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29

end QiushiMatmul
