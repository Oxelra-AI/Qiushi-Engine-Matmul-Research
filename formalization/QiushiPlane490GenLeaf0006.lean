import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0006Refs : Fin 44 → RowRef 713 43 := ![.occ 89, .occ 90, .occ 93, .occ 99, .occ 100, .occ 102, .occ 107, .occ 110, .occ 134, .occ 135, .occ 197, .occ 210, .occ 216, .occ 236, .occ 283, .occ 284, .occ 300, .occ 303, .occ 308, .occ 335, .occ 354, .occ 364, .occ 447, .occ 503, .occ 532, .occ 575, .occ 584, .occ 599, .occ 601, .occ 617, .occ 653, .occ 667, .occ 679, .occ 692, .occ 704, .sumGe, .branchLe 29 (0), .branchLe 4 (0), .branchLe 23 (0), .branchLe 16 (0), .branchLe 39 (0), .branchGe 19 (1), .branchLe 30 (0), .branchGe 25 (1)]

def plane490GenLeaf0006Mult : Fin 44 → Nat := ![231, 117, 91, 373, 303, 83, 587, 977, 194, 534, 200, 176, 225, 197, 174, 64, 556, 220, 660, 451, 156, 402, 199, 113, 26, 48, 21, 41, 279, 248, 59, 278, 166, 55, 61, 1105, 386, 1105, 364, 1050, 1003, 2254, 703, 3178]

theorem plane490GenLeaf0006 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0006Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0006Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0006Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0006Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 89
  · exact hroot.hOcc 90
  · exact hroot.hOcc 93
  · exact hroot.hOcc 99
  · exact hroot.hOcc 100
  · exact hroot.hOcc 102
  · exact hroot.hOcc 107
  · exact hroot.hOcc 110
  · exact hroot.hOcc 134
  · exact hroot.hOcc 135
  · exact hroot.hOcc 197
  · exact hroot.hOcc 210
  · exact hroot.hOcc 216
  · exact hroot.hOcc 236
  · exact hroot.hOcc 283
  · exact hroot.hOcc 284
  · exact hroot.hOcc 300
  · exact hroot.hOcc 303
  · exact hroot.hOcc 308
  · exact hroot.hOcc 335
  · exact hroot.hOcc 354
  · exact hroot.hOcc 364
  · exact hroot.hOcc 447
  · exact hroot.hOcc 503
  · exact hroot.hOcc 532
  · exact hroot.hOcc 575
  · exact hroot.hOcc 584
  · exact hroot.hOcc 599
  · exact hroot.hOcc 601
  · exact hroot.hOcc 617
  · exact hroot.hOcc 653
  · exact hroot.hOcc 667
  · exact hroot.hOcc 679
  · exact hroot.hOcc 692
  · exact hroot.hOcc 704
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25

end QiushiMatmul
