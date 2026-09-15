import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0078Refs : Fin 50 → RowRef 726 49 := ![.occ 98, .occ 105, .occ 114, .occ 118, .occ 124, .occ 175, .occ 214, .occ 216, .occ 217, .occ 219, .occ 223, .occ 244, .occ 315, .occ 334, .occ 355, .occ 365, .occ 366, .occ 367, .occ 370, .occ 372, .occ 374, .occ 377, .occ 393, .occ 400, .occ 410, .occ 418, .occ 482, .occ 484, .occ 510, .occ 517, .occ 548, .occ 565, .occ 571, .occ 585, .occ 603, .occ 630, .occ 640, .occ 643, .occ 669, .occ 687, .occ 704, .occ 711, .sumGe, .branchGe 31 (1), .branchLe 44 (0), .branchLe 11 (0), .branchLe 27 (0), .branchLe 22 (0), .branchGe 15 (1), .branchGe 48 (1)]

def plane491GenLeaf0078Mult : Fin 50 → Nat := ![2034, 438, 1566, 3636, 3554, 996, 6205, 1003, 232, 2038, 741, 479, 484, 1001, 493, 2168, 1483, 1872, 2258, 2717, 1701, 374, 1140, 193, 1102, 166, 1081, 235, 1208, 1013, 129, 1768, 594, 235, 1933, 144, 985, 151, 561, 737, 2383, 1356, 7973, 15563, 6753, 7636, 4322, 4488, 7720, 23518]

theorem plane491GenLeaf0078 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_48 : (1 : Int) ≤ x 48)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0078Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0078Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0078Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0078Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 98
  · exact hroot.hOcc 105
  · exact hroot.hOcc 114
  · exact hroot.hOcc 118
  · exact hroot.hOcc 124
  · exact hroot.hOcc 175
  · exact hroot.hOcc 214
  · exact hroot.hOcc 216
  · exact hroot.hOcc 217
  · exact hroot.hOcc 219
  · exact hroot.hOcc 223
  · exact hroot.hOcc 244
  · exact hroot.hOcc 315
  · exact hroot.hOcc 334
  · exact hroot.hOcc 355
  · exact hroot.hOcc 365
  · exact hroot.hOcc 366
  · exact hroot.hOcc 367
  · exact hroot.hOcc 370
  · exact hroot.hOcc 372
  · exact hroot.hOcc 374
  · exact hroot.hOcc 377
  · exact hroot.hOcc 393
  · exact hroot.hOcc 400
  · exact hroot.hOcc 410
  · exact hroot.hOcc 418
  · exact hroot.hOcc 482
  · exact hroot.hOcc 484
  · exact hroot.hOcc 510
  · exact hroot.hOcc 517
  · exact hroot.hOcc 548
  · exact hroot.hOcc 565
  · exact hroot.hOcc 571
  · exact hroot.hOcc 585
  · exact hroot.hOcc 603
  · exact hroot.hOcc 630
  · exact hroot.hOcc 640
  · exact hroot.hOcc 643
  · exact hroot.hOcc 669
  · exact hroot.hOcc 687
  · exact hroot.hOcc 704
  · exact hroot.hOcc 711
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (11 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (22 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (15 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (48 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_48

end QiushiMatmul
