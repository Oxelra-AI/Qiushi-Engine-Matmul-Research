import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0047Refs : Fin 49 → RowRef 668 48 := ![.occ 83, .occ 85, .occ 89, .occ 100, .occ 103, .occ 162, .occ 165, .occ 227, .occ 231, .occ 260, .occ 294, .occ 308, .occ 347, .occ 356, .occ 364, .occ 386, .occ 401, .occ 414, .occ 470, .occ 497, .occ 509, .occ 527, .occ 536, .occ 544, .occ 563, .occ 566, .occ 604, .occ 621, .occ 644, .occ 648, .occ 649, .occ 650, .occ 661, .occ 664, .occ 666, .sumGe, .branchGe 39 (1), .branchLe 7 (0), .branchLe 28 (0), .branchLe 40 (0), .branchLe 29 (0), .branchLe 19 (0), .branchLe 36 (0), .branchLe 23 (0), .branchLe 45 (0), .branchLe 5 (0), .branchLe 25 (0), .branchLe 30 (0), .branchLe 2 (0)]

def plane487GenLeaf0047Mult : Fin 49 → Nat := ![171494, 33524, 310204, 137936, 107768, 282812, 277768, 34852, 161810, 184702, 48188, 28158, 92778, 168666, 38346, 127554, 82032, 179420, 10638, 34362, 83014, 40438, 92336, 9244, 9966, 10760, 31292, 26434, 15552, 97805, 6871, 177618, 163227, 19447, 10957, 620951, 742378, 390968, 176400, 295318, 470516, 488294, 302076, 527570, 516496, 528520, 169542, 307092, 436462]

theorem plane487GenLeaf0047 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_45 : x 45 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0047Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0047Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0047Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0047Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 83
  · exact hroot.hOcc 85
  · exact hroot.hOcc 89
  · exact hroot.hOcc 100
  · exact hroot.hOcc 103
  · exact hroot.hOcc 162
  · exact hroot.hOcc 165
  · exact hroot.hOcc 227
  · exact hroot.hOcc 231
  · exact hroot.hOcc 260
  · exact hroot.hOcc 294
  · exact hroot.hOcc 308
  · exact hroot.hOcc 347
  · exact hroot.hOcc 356
  · exact hroot.hOcc 364
  · exact hroot.hOcc 386
  · exact hroot.hOcc 401
  · exact hroot.hOcc 414
  · exact hroot.hOcc 470
  · exact hroot.hOcc 497
  · exact hroot.hOcc 509
  · exact hroot.hOcc 527
  · exact hroot.hOcc 536
  · exact hroot.hOcc 544
  · exact hroot.hOcc 563
  · exact hroot.hOcc 566
  · exact hroot.hOcc 604
  · exact hroot.hOcc 621
  · exact hroot.hOcc 644
  · exact hroot.hOcc 648
  · exact hroot.hOcc 649
  · exact hroot.hOcc 650
  · exact hroot.hOcc 661
  · exact hroot.hOcc 664
  · exact hroot.hOcc 666
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (39 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (7 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (28 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (40 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (29 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (19 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (36 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (45 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_45
  · change (∑ k, (if k = (5 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (25 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (30 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (2 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2

end QiushiMatmul
