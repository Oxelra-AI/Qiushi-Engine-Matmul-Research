import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0091Refs : Fin 50 → RowRef 726 49 := ![.occ 83, .occ 98, .occ 99, .occ 103, .occ 118, .occ 124, .occ 127, .occ 167, .occ 168, .occ 169, .occ 215, .occ 220, .occ 248, .occ 292, .occ 315, .occ 341, .occ 355, .occ 417, .occ 426, .occ 432, .occ 484, .occ 487, .occ 490, .occ 525, .occ 532, .occ 534, .occ 565, .occ 567, .occ 574, .occ 582, .occ 597, .occ 603, .occ 611, .occ 621, .occ 630, .occ 662, .occ 686, .occ 687, .occ 718, .sumGe, .nonneg 18, .branchGe 31 (1), .branchLe 44 (0), .branchGe 11 (1), .branchLe 2 (0), .branchLe 7 (0), .branchGe 39 (1), .branchLe 8 (0), .branchLe 27 (0), .branchLe 43 (0)]

def plane491GenLeaf0091Mult : Fin 50 → Nat := ![794, 32175, 90078, 66494, 142853, 18748, 17107, 17697, 4679, 61880, 7541, 11716, 35941, 2650, 46962, 48308, 95233, 9270, 69376, 13129, 7983, 5258, 8900, 5525, 19791, 7175, 5970, 23269, 53127, 32898, 4802, 2132, 11665, 31285, 32066, 6795, 15554, 31518, 5330, 142853, 19377, 415210, 142853, 350840, 125879, 89919, 129928, 88157, 107919, 109955]

theorem plane491GenLeaf0091 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_43 : x 43 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0091Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0091Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0091Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0091Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 83
  · exact hroot.hOcc 98
  · exact hroot.hOcc 99
  · exact hroot.hOcc 103
  · exact hroot.hOcc 118
  · exact hroot.hOcc 124
  · exact hroot.hOcc 127
  · exact hroot.hOcc 167
  · exact hroot.hOcc 168
  · exact hroot.hOcc 169
  · exact hroot.hOcc 215
  · exact hroot.hOcc 220
  · exact hroot.hOcc 248
  · exact hroot.hOcc 292
  · exact hroot.hOcc 315
  · exact hroot.hOcc 341
  · exact hroot.hOcc 355
  · exact hroot.hOcc 417
  · exact hroot.hOcc 426
  · exact hroot.hOcc 432
  · exact hroot.hOcc 484
  · exact hroot.hOcc 487
  · exact hroot.hOcc 490
  · exact hroot.hOcc 525
  · exact hroot.hOcc 532
  · exact hroot.hOcc 534
  · exact hroot.hOcc 565
  · exact hroot.hOcc 567
  · exact hroot.hOcc 574
  · exact hroot.hOcc 582
  · exact hroot.hOcc 597
  · exact hroot.hOcc 603
  · exact hroot.hOcc 611
  · exact hroot.hOcc 621
  · exact hroot.hOcc 630
  · exact hroot.hOcc 662
  · exact hroot.hOcc 686
  · exact hroot.hOcc 687
  · exact hroot.hOcc 718
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (18 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (11 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11
  · change (∑ k, (if k = (2 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (7 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (39 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (8 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (43 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43

end QiushiMatmul
