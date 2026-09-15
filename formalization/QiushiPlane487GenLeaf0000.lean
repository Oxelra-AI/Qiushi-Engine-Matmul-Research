import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0000Refs : Fin 49 → RowRef 668 48 := ![.occ 81, .occ 89, .occ 98, .occ 107, .occ 122, .occ 183, .occ 192, .occ 223, .occ 233, .occ 253, .occ 269, .occ 275, .occ 297, .occ 303, .occ 308, .occ 352, .occ 378, .occ 379, .occ 386, .occ 387, .occ 390, .occ 391, .occ 399, .occ 412, .occ 415, .occ 425, .occ 488, .occ 536, .occ 550, .occ 572, .occ 581, .occ 609, .occ 625, .occ 630, .occ 637, .occ 639, .occ 656, .occ 662, .occ 664, .sumGe, .branchLe 39 (0), .branchLe 23 (0), .branchLe 6 (0), .branchLe 25 (0), .branchLe 12 (0), .branchLe 15 (0), .branchLe 16 (0), .branchLe 38 (0), .branchLe 9 (0)]

def plane487GenLeaf0000Mult : Fin 49 → Nat := ![1012437, 5474961, 4135274, 11635356, 6716939, 235779, 4175367, 3130996, 711033, 1532590, 5628931, 3036841, 12444055, 11436136, 3322440, 2453353, 479419, 10890016, 4605205, 3141063, 1207231, 1234228, 1942925, 7414289, 982533, 790183, 2499646, 8682194, 1751683, 2985361, 3303635, 6473769, 5624974, 4828455, 1031835, 2289482, 6172819, 562829, 2537483, 34209562, 31109250, 12468889, 32747610, 25382785, 23209778, 21009417, 29977155, 28370129, 29382597]

theorem plane487GenLeaf0000 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0000Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0000Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 81
  · exact hroot.hOcc 89
  · exact hroot.hOcc 98
  · exact hroot.hOcc 107
  · exact hroot.hOcc 122
  · exact hroot.hOcc 183
  · exact hroot.hOcc 192
  · exact hroot.hOcc 223
  · exact hroot.hOcc 233
  · exact hroot.hOcc 253
  · exact hroot.hOcc 269
  · exact hroot.hOcc 275
  · exact hroot.hOcc 297
  · exact hroot.hOcc 303
  · exact hroot.hOcc 308
  · exact hroot.hOcc 352
  · exact hroot.hOcc 378
  · exact hroot.hOcc 379
  · exact hroot.hOcc 386
  · exact hroot.hOcc 387
  · exact hroot.hOcc 390
  · exact hroot.hOcc 391
  · exact hroot.hOcc 399
  · exact hroot.hOcc 412
  · exact hroot.hOcc 415
  · exact hroot.hOcc 425
  · exact hroot.hOcc 488
  · exact hroot.hOcc 536
  · exact hroot.hOcc 550
  · exact hroot.hOcc 572
  · exact hroot.hOcc 581
  · exact hroot.hOcc 609
  · exact hroot.hOcc 625
  · exact hroot.hOcc 630
  · exact hroot.hOcc 637
  · exact hroot.hOcc 639
  · exact hroot.hOcc 656
  · exact hroot.hOcc 662
  · exact hroot.hOcc 664
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (6 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (25 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (12 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (15 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (16 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (38 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (9 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9

end QiushiMatmul
