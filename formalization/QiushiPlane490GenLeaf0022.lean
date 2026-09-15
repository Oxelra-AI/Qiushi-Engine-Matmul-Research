import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0022Refs : Fin 44 → RowRef 713 43 := ![.occ 85, .occ 89, .occ 90, .occ 95, .occ 109, .occ 127, .occ 131, .occ 133, .occ 141, .occ 196, .occ 198, .occ 200, .occ 236, .occ 238, .occ 249, .occ 277, .occ 283, .occ 303, .occ 309, .occ 364, .occ 479, .occ 486, .occ 491, .occ 494, .occ 503, .occ 520, .occ 521, .occ 536, .occ 549, .occ 552, .occ 555, .occ 578, .occ 649, .occ 704, .occ 710, .sumGe, .branchLe 29 (0), .branchLe 4 (0), .branchLe 23 (0), .branchGe 16 (1), .branchGe 15 (1), .branchLe 32 (0), .branchGe 3 (1), .branchLe 33 (0)]

def plane490GenLeaf0022Mult : Fin 44 → Nat := ![1689, 1340, 1764, 2087, 366, 727, 773, 1909, 852, 161, 83, 1160, 587, 438, 387, 211, 1127, 3, 550, 353, 26, 301, 125, 415, 8, 62, 96, 41, 226, 769, 81, 508, 28, 787, 237, 2324, 2228, 1655, 2023, 4347, 2713, 1813, 7545, 2087]

theorem plane490GenLeaf0022 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0022Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0022Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0022Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0022Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 85
  · exact hroot.hOcc 89
  · exact hroot.hOcc 90
  · exact hroot.hOcc 95
  · exact hroot.hOcc 109
  · exact hroot.hOcc 127
  · exact hroot.hOcc 131
  · exact hroot.hOcc 133
  · exact hroot.hOcc 141
  · exact hroot.hOcc 196
  · exact hroot.hOcc 198
  · exact hroot.hOcc 200
  · exact hroot.hOcc 236
  · exact hroot.hOcc 238
  · exact hroot.hOcc 249
  · exact hroot.hOcc 277
  · exact hroot.hOcc 283
  · exact hroot.hOcc 303
  · exact hroot.hOcc 309
  · exact hroot.hOcc 364
  · exact hroot.hOcc 479
  · exact hroot.hOcc 486
  · exact hroot.hOcc 491
  · exact hroot.hOcc 494
  · exact hroot.hOcc 503
  · exact hroot.hOcc 520
  · exact hroot.hOcc 521
  · exact hroot.hOcc 536
  · exact hroot.hOcc 549
  · exact hroot.hOcc 552
  · exact hroot.hOcc 555
  · exact hroot.hOcc 578
  · exact hroot.hOcc 649
  · exact hroot.hOcc 704
  · exact hroot.hOcc 710
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3
  · change (∑ k, (if k = (33 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33

end QiushiMatmul
