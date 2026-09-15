import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0029Refs : Fin 44 → RowRef 713 43 := ![.occ 84, .occ 85, .occ 86, .occ 94, .occ 106, .occ 109, .occ 117, .occ 205, .occ 219, .occ 239, .occ 261, .occ 293, .occ 326, .occ 336, .occ 354, .occ 362, .occ 364, .occ 372, .occ 386, .occ 450, .occ 453, .occ 494, .occ 509, .occ 518, .occ 533, .occ 575, .occ 609, .occ 664, .occ 665, .occ 679, .occ 698, .occ 710, .sumGe, .branchLe 29 (0), .branchLe 4 (0), .branchGe 23 (1), .branchLe 30 (0), .branchLe 28 (0), .branchLe 35 (0), .branchLe 5 (0), .branchLe 38 (0), .branchLe 25 (0), .branchLe 15 (0), .branchGe 24 (1)]

def plane490GenLeaf0029Mult : Fin 44 → Nat := ![2311, 1374, 605, 681, 2114, 2870, 935, 1242, 2639, 1291, 1632, 876, 2148, 3926, 4350, 2622, 442, 646, 2956, 1609, 459, 1030, 2457, 1638, 810, 536, 396, 2806, 611, 3859, 432, 923, 9658, 7201, 9226, 5887, 3539, 5303, 9047, 8416, 3632, 3699, 9658, 18998]

theorem plane490GenLeaf0029 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0029Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0029Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0029Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0029Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 84
  · exact hroot.hOcc 85
  · exact hroot.hOcc 86
  · exact hroot.hOcc 94
  · exact hroot.hOcc 106
  · exact hroot.hOcc 109
  · exact hroot.hOcc 117
  · exact hroot.hOcc 205
  · exact hroot.hOcc 219
  · exact hroot.hOcc 239
  · exact hroot.hOcc 261
  · exact hroot.hOcc 293
  · exact hroot.hOcc 326
  · exact hroot.hOcc 336
  · exact hroot.hOcc 354
  · exact hroot.hOcc 362
  · exact hroot.hOcc 364
  · exact hroot.hOcc 372
  · exact hroot.hOcc 386
  · exact hroot.hOcc 450
  · exact hroot.hOcc 453
  · exact hroot.hOcc 494
  · exact hroot.hOcc 509
  · exact hroot.hOcc 518
  · exact hroot.hOcc 533
  · exact hroot.hOcc 575
  · exact hroot.hOcc 609
  · exact hroot.hOcc 664
  · exact hroot.hOcc 665
  · exact hroot.hOcc 679
  · exact hroot.hOcc 698
  · exact hroot.hOcc 710
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (38 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24

end QiushiMatmul
