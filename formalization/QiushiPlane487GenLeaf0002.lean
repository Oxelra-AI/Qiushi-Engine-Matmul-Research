import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0002Refs : Fin 49 → RowRef 668 48 := ![.occ 83, .occ 86, .occ 103, .occ 198, .occ 220, .occ 223, .occ 224, .occ 227, .occ 231, .occ 232, .occ 240, .occ 246, .occ 269, .occ 275, .occ 280, .occ 297, .occ 303, .occ 316, .occ 356, .occ 380, .occ 386, .occ 387, .occ 402, .occ 415, .occ 425, .occ 521, .occ 572, .occ 577, .occ 604, .occ 609, .occ 625, .occ 632, .occ 639, .occ 651, .occ 652, .occ 665, .sumGe, .nonneg 7, .branchLe 39 (0), .branchLe 23 (0), .branchLe 6 (0), .branchLe 25 (0), .branchLe 12 (0), .branchLe 15 (0), .branchLe 16 (0), .branchLe 38 (0), .branchGe 9 (1), .branchLe 33 (0), .branchGe 19 (1)]

def plane487GenLeaf0002Mult : Fin 49 → Nat := ![1284508, 2804429, 266248, 2167507, 346242, 1378195, 1094943, 768097, 1289251, 31290, 948214, 823979, 308523, 97657, 796146, 1030298, 2111053, 2641433, 2177, 406180, 877086, 681850, 270341, 247193, 1273848, 451927, 235630, 693898, 932641, 1146933, 369516, 1042140, 515166, 282551, 648784, 207624, 5322936, 771710, 5115312, 3262168, 1962939, 4393044, 3592578, 2163322, 4525219, 3513209, 961365, 4082837, 13263461]

theorem plane487GenLeaf0002 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0002Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0002Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0002Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0002Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 83
  · exact hroot.hOcc 86
  · exact hroot.hOcc 103
  · exact hroot.hOcc 198
  · exact hroot.hOcc 220
  · exact hroot.hOcc 223
  · exact hroot.hOcc 224
  · exact hroot.hOcc 227
  · exact hroot.hOcc 231
  · exact hroot.hOcc 232
  · exact hroot.hOcc 240
  · exact hroot.hOcc 246
  · exact hroot.hOcc 269
  · exact hroot.hOcc 275
  · exact hroot.hOcc 280
  · exact hroot.hOcc 297
  · exact hroot.hOcc 303
  · exact hroot.hOcc 316
  · exact hroot.hOcc 356
  · exact hroot.hOcc 380
  · exact hroot.hOcc 386
  · exact hroot.hOcc 387
  · exact hroot.hOcc 402
  · exact hroot.hOcc 415
  · exact hroot.hOcc 425
  · exact hroot.hOcc 521
  · exact hroot.hOcc 572
  · exact hroot.hOcc 577
  · exact hroot.hOcc 604
  · exact hroot.hOcc 609
  · exact hroot.hOcc 625
  · exact hroot.hOcc 632
  · exact hroot.hOcc 639
  · exact hroot.hOcc 651
  · exact hroot.hOcc 652
  · exact hroot.hOcc 665
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
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
  · change (∑ k, (if k = (19 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19

end QiushiMatmul
