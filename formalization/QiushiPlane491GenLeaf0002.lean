import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0002Refs : Fin 50 → RowRef 726 49 := ![.occ 79, .occ 81, .occ 105, .occ 111, .occ 114, .occ 119, .occ 124, .occ 144, .occ 200, .occ 219, .occ 220, .occ 237, .occ 245, .occ 254, .occ 256, .occ 257, .occ 287, .occ 320, .occ 326, .occ 341, .occ 370, .occ 414, .occ 431, .occ 504, .occ 506, .occ 532, .occ 533, .occ 541, .occ 559, .occ 563, .occ 584, .occ 643, .occ 687, .occ 698, .occ 712, .occ 723, .occ 724, .sumGe, .nonneg 1, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchLe 29 (0), .branchLe 46 (0), .branchLe 32 (0), .branchLe 38 (0), .branchLe 6 (0), .branchLe 9 (0), .branchLe 4 (0), .branchGe 0 (1)]

def plane491GenLeaf0002Mult : Fin 50 → Nat := ![2712, 139016, 83239, 3164, 23735, 54090, 136968, 24757, 81872, 48462, 29923, 165901, 4278, 86064, 33561, 152910, 28422, 65504, 8197, 55574, 59136, 7937, 57279, 45493, 103515, 173455, 107677, 29495, 43261, 49538, 23963, 31732, 109777, 55299, 21535, 71053, 24427, 447443, 53157, 266613, 139860, 268471, 174690, 317254, 399053, 358432, 425908, 377446, 200388, 791470]

theorem plane491GenLeaf0002 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hUB_46 : x 46 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_38 : x 38 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0002Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0002Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0002Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0002Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 79
  · exact hroot.hOcc 81
  · exact hroot.hOcc 105
  · exact hroot.hOcc 111
  · exact hroot.hOcc 114
  · exact hroot.hOcc 119
  · exact hroot.hOcc 124
  · exact hroot.hOcc 144
  · exact hroot.hOcc 200
  · exact hroot.hOcc 219
  · exact hroot.hOcc 220
  · exact hroot.hOcc 237
  · exact hroot.hOcc 245
  · exact hroot.hOcc 254
  · exact hroot.hOcc 256
  · exact hroot.hOcc 257
  · exact hroot.hOcc 287
  · exact hroot.hOcc 320
  · exact hroot.hOcc 326
  · exact hroot.hOcc 341
  · exact hroot.hOcc 370
  · exact hroot.hOcc 414
  · exact hroot.hOcc 431
  · exact hroot.hOcc 504
  · exact hroot.hOcc 506
  · exact hroot.hOcc 532
  · exact hroot.hOcc 533
  · exact hroot.hOcc 541
  · exact hroot.hOcc 559
  · exact hroot.hOcc 563
  · exact hroot.hOcc 584
  · exact hroot.hOcc 643
  · exact hroot.hOcc 687
  · exact hroot.hOcc 698
  · exact hroot.hOcc 712
  · exact hroot.hOcc 723
  · exact hroot.hOcc 724
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (1 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (46 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_46
  · change (∑ k, (if k = (32 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (38 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (6 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (9 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (4 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (0 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
