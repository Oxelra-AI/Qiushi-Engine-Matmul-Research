import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0045Refs : Fin 50 → RowRef 726 49 := ![.occ 79, .occ 81, .occ 102, .occ 105, .occ 108, .occ 114, .occ 128, .occ 166, .occ 190, .occ 200, .occ 204, .occ 211, .occ 219, .occ 254, .occ 267, .occ 320, .occ 325, .occ 341, .occ 345, .occ 361, .occ 372, .occ 375, .occ 389, .occ 401, .occ 431, .occ 445, .occ 493, .occ 508, .occ 509, .occ 526, .occ 549, .occ 552, .occ 558, .occ 594, .occ 628, .occ 654, .occ 686, .occ 691, .occ 718, .occ 725, .sumGe, .nonneg 40, .nonneg 46, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchGe 29 (1), .branchGe 43 (1), .branchLe 32 (0), .branchGe 0 (1)]

def plane491GenLeaf0045Mult : Fin 50 → Nat := ![176688, 279575, 82378, 80437, 238489, 36263, 55986, 222699, 177379, 205198, 44816, 4460, 25647, 14983, 82378, 39914, 61109, 11721, 71368, 39990, 36874, 32928, 93412, 190548, 79278, 4505, 43670, 21554, 15098, 117880, 13717, 17695, 43763, 20576, 32244, 136964, 21997, 93200, 8274, 38760, 313496, 72977, 131896, 274736, 261019, 298398, 694579, 1294559, 105253, 1035764]

theorem plane491GenLeaf0045 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_43 : (1 : Int) ≤ x 43)
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0045Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0045Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0045Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0045Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 79
  · exact hroot.hOcc 81
  · exact hroot.hOcc 102
  · exact hroot.hOcc 105
  · exact hroot.hOcc 108
  · exact hroot.hOcc 114
  · exact hroot.hOcc 128
  · exact hroot.hOcc 166
  · exact hroot.hOcc 190
  · exact hroot.hOcc 200
  · exact hroot.hOcc 204
  · exact hroot.hOcc 211
  · exact hroot.hOcc 219
  · exact hroot.hOcc 254
  · exact hroot.hOcc 267
  · exact hroot.hOcc 320
  · exact hroot.hOcc 325
  · exact hroot.hOcc 341
  · exact hroot.hOcc 345
  · exact hroot.hOcc 361
  · exact hroot.hOcc 372
  · exact hroot.hOcc 375
  · exact hroot.hOcc 389
  · exact hroot.hOcc 401
  · exact hroot.hOcc 431
  · exact hroot.hOcc 445
  · exact hroot.hOcc 493
  · exact hroot.hOcc 508
  · exact hroot.hOcc 509
  · exact hroot.hOcc 526
  · exact hroot.hOcc 549
  · exact hroot.hOcc 552
  · exact hroot.hOcc 558
  · exact hroot.hOcc 594
  · exact hroot.hOcc 628
  · exact hroot.hOcc 654
  · exact hroot.hOcc 686
  · exact hroot.hOcc 691
  · exact hroot.hOcc 718
  · exact hroot.hOcc 725
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (40 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (46 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (43 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_43
  · change (∑ k, (if k = (32 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (0 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
