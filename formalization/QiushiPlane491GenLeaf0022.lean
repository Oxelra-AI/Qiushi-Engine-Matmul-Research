import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0022Refs : Fin 50 → RowRef 726 49 := ![.occ 80, .occ 87, .occ 99, .occ 122, .occ 134, .occ 144, .occ 173, .occ 174, .occ 230, .occ 240, .occ 243, .occ 257, .occ 263, .occ 294, .occ 317, .occ 333, .occ 340, .occ 365, .occ 379, .occ 396, .occ 401, .occ 410, .occ 423, .occ 431, .occ 466, .occ 476, .occ 477, .occ 493, .occ 516, .occ 535, .occ 552, .occ 554, .occ 559, .occ 573, .occ 584, .occ 594, .occ 671, .occ 681, .occ 705, .occ 721, .sumGe, .nonneg 48, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchLe 29 (0), .branchLe 46 (0), .branchGe 32 (1), .branchLe 28 (0), .branchGe 22 (1)]

def plane491GenLeaf0022Mult : Fin 50 → Nat := ![85511, 204447, 228979, 74601, 15239, 109111, 30765, 51101, 15694, 87182, 19439, 5445, 81206, 18868, 69717, 11084, 6913, 97546, 37998, 52769, 18036, 33712, 135824, 102674, 123158, 17685, 51, 81889, 4640, 66458, 15968, 52266, 78983, 7495, 76625, 24364, 7024, 93373, 6957, 46065, 312566, 21825, 162761, 187518, 162251, 270166, 117032, 990551, 173908, 883922]

theorem plane491GenLeaf0022 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hUB_46 : x 46 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0022Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0022Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0022Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0022Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 80
  · exact hroot.hOcc 87
  · exact hroot.hOcc 99
  · exact hroot.hOcc 122
  · exact hroot.hOcc 134
  · exact hroot.hOcc 144
  · exact hroot.hOcc 173
  · exact hroot.hOcc 174
  · exact hroot.hOcc 230
  · exact hroot.hOcc 240
  · exact hroot.hOcc 243
  · exact hroot.hOcc 257
  · exact hroot.hOcc 263
  · exact hroot.hOcc 294
  · exact hroot.hOcc 317
  · exact hroot.hOcc 333
  · exact hroot.hOcc 340
  · exact hroot.hOcc 365
  · exact hroot.hOcc 379
  · exact hroot.hOcc 396
  · exact hroot.hOcc 401
  · exact hroot.hOcc 410
  · exact hroot.hOcc 423
  · exact hroot.hOcc 431
  · exact hroot.hOcc 466
  · exact hroot.hOcc 476
  · exact hroot.hOcc 477
  · exact hroot.hOcc 493
  · exact hroot.hOcc 516
  · exact hroot.hOcc 535
  · exact hroot.hOcc 552
  · exact hroot.hOcc 554
  · exact hroot.hOcc 559
  · exact hroot.hOcc 573
  · exact hroot.hOcc 584
  · exact hroot.hOcc 594
  · exact hroot.hOcc 671
  · exact hroot.hOcc 681
  · exact hroot.hOcc 705
  · exact hroot.hOcc 721
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (48 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (46 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_46
  · change (∑ k, (if k = (32 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32
  · change (∑ k, (if k = (28 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (22 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22

end QiushiMatmul
