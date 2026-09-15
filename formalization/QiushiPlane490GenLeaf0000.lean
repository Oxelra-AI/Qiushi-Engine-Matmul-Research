import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0000Refs : Fin 44 → RowRef 713 43 := ![.occ 84, .occ 89, .occ 90, .occ 104, .occ 109, .occ 113, .occ 114, .occ 120, .occ 203, .occ 236, .occ 237, .occ 251, .occ 281, .occ 284, .occ 295, .occ 303, .occ 335, .occ 354, .occ 362, .occ 449, .occ 466, .occ 467, .occ 481, .occ 493, .occ 518, .occ 520, .occ 528, .occ 533, .occ 585, .occ 603, .occ 653, .occ 664, .occ 689, .occ 692, .sumGe, .branchLe 29 (0), .branchLe 4 (0), .branchLe 23 (0), .branchLe 16 (0), .branchLe 39 (0), .branchLe 19 (0), .branchLe 10 (0), .branchLe 30 (0), .branchLe 12 (0)]

def plane490GenLeaf0000Mult : Fin 44 → Nat := ![76760, 37704, 11138, 74393, 34993, 18642, 23440, 38277, 40985, 4321, 30541, 10712, 2833, 20594, 24053, 36873, 63651, 548, 38812, 25969, 12196, 5759, 41906, 28409, 32966, 4330, 6718, 43503, 2754, 12865, 46633, 276, 16847, 25122, 175312, 128679, 126198, 158465, 150190, 164947, 170715, 103534, 175312, 135137]

theorem plane490GenLeaf0000 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0000Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0000Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 84
  · exact hroot.hOcc 89
  · exact hroot.hOcc 90
  · exact hroot.hOcc 104
  · exact hroot.hOcc 109
  · exact hroot.hOcc 113
  · exact hroot.hOcc 114
  · exact hroot.hOcc 120
  · exact hroot.hOcc 203
  · exact hroot.hOcc 236
  · exact hroot.hOcc 237
  · exact hroot.hOcc 251
  · exact hroot.hOcc 281
  · exact hroot.hOcc 284
  · exact hroot.hOcc 295
  · exact hroot.hOcc 303
  · exact hroot.hOcc 335
  · exact hroot.hOcc 354
  · exact hroot.hOcc 362
  · exact hroot.hOcc 449
  · exact hroot.hOcc 466
  · exact hroot.hOcc 467
  · exact hroot.hOcc 481
  · exact hroot.hOcc 493
  · exact hroot.hOcc 518
  · exact hroot.hOcc 520
  · exact hroot.hOcc 528
  · exact hroot.hOcc 533
  · exact hroot.hOcc 585
  · exact hroot.hOcc 603
  · exact hroot.hOcc 653
  · exact hroot.hOcc 664
  · exact hroot.hOcc 689
  · exact hroot.hOcc 692
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (12 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12

end QiushiMatmul
