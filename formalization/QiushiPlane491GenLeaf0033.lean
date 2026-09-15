import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0033Refs : Fin 49 → RowRef 726 49 := ![.occ 94, .occ 97, .occ 104, .occ 105, .occ 116, .occ 120, .occ 122, .occ 125, .occ 143, .occ 158, .occ 166, .occ 218, .occ 228, .occ 241, .occ 244, .occ 260, .occ 292, .occ 324, .occ 364, .occ 372, .occ 400, .occ 402, .occ 420, .occ 431, .occ 464, .occ 486, .occ 487, .occ 494, .occ 504, .occ 508, .occ 558, .occ 575, .occ 603, .occ 621, .occ 628, .occ 632, .occ 685, .sumGe, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchGe 29 (1), .branchLe 43 (0), .branchLe 9 (0), .branchLe 5 (0), .branchLe 44 (0), .branchLe 24 (0), .branchGe 4 (1), .branchLe 21 (0)]

def plane491GenLeaf0033Mult : Fin 49 → Nat := ![8202, 926, 34728, 3367, 19020, 20701, 25215, 2783, 3328, 24046, 10085, 9364, 5253, 7102, 10044, 25184, 7785, 13973, 22020, 73, 3424, 19127, 11935, 8286, 2269, 12885, 12437, 13992, 224, 11547, 4621, 5559, 2038, 219, 7816, 16249, 14911, 56482, 56482, 41123, 40233, 103669, 50923, 18499, 5033, 42490, 32112, 124642, 40438]

theorem plane491GenLeaf0033 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_43 : x 43 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0033Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0033Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0033Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0033Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 94
  · exact hroot.hOcc 97
  · exact hroot.hOcc 104
  · exact hroot.hOcc 105
  · exact hroot.hOcc 116
  · exact hroot.hOcc 120
  · exact hroot.hOcc 122
  · exact hroot.hOcc 125
  · exact hroot.hOcc 143
  · exact hroot.hOcc 158
  · exact hroot.hOcc 166
  · exact hroot.hOcc 218
  · exact hroot.hOcc 228
  · exact hroot.hOcc 241
  · exact hroot.hOcc 244
  · exact hroot.hOcc 260
  · exact hroot.hOcc 292
  · exact hroot.hOcc 324
  · exact hroot.hOcc 364
  · exact hroot.hOcc 372
  · exact hroot.hOcc 400
  · exact hroot.hOcc 402
  · exact hroot.hOcc 420
  · exact hroot.hOcc 431
  · exact hroot.hOcc 464
  · exact hroot.hOcc 486
  · exact hroot.hOcc 487
  · exact hroot.hOcc 494
  · exact hroot.hOcc 504
  · exact hroot.hOcc 508
  · exact hroot.hOcc 558
  · exact hroot.hOcc 575
  · exact hroot.hOcc 603
  · exact hroot.hOcc 621
  · exact hroot.hOcc 628
  · exact hroot.hOcc 632
  · exact hroot.hOcc 685
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (43 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (9 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (5 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (44 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (24 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (4 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (21 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21

end QiushiMatmul
