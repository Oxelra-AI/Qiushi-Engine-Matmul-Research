import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0004Refs : Fin 44 → RowRef 713 43 := ![.occ 91, .occ 93, .occ 106, .occ 109, .occ 114, .occ 117, .occ 123, .occ 147, .occ 148, .occ 196, .occ 202, .occ 218, .occ 234, .occ 238, .occ 283, .occ 291, .occ 298, .occ 302, .occ 303, .occ 314, .occ 320, .occ 333, .occ 342, .occ 364, .occ 385, .occ 447, .occ 449, .occ 503, .occ 522, .occ 548, .occ 566, .occ 603, .occ 617, .occ 703, .occ 710, .sumGe, .branchLe 29 (0), .branchLe 4 (0), .branchLe 23 (0), .branchLe 16 (0), .branchLe 39 (0), .branchLe 19 (0), .branchGe 10 (1), .branchGe 27 (1)]

def plane490GenLeaf0004Mult : Fin 44 → Nat := ![566, 902, 1941, 5127, 1855, 2434, 815, 93, 564, 891, 270, 1688, 320, 3448, 937, 905, 103, 2103, 747, 190, 157, 107, 639, 2503, 170, 30, 1809, 1032, 480, 3, 485, 2066, 1519, 739, 274, 5401, 4395, 1269, 1779, 5127, 5401, 1689, 9389, 11857]

theorem plane490GenLeaf0004 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0004Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0004Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0004Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0004Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 91
  · exact hroot.hOcc 93
  · exact hroot.hOcc 106
  · exact hroot.hOcc 109
  · exact hroot.hOcc 114
  · exact hroot.hOcc 117
  · exact hroot.hOcc 123
  · exact hroot.hOcc 147
  · exact hroot.hOcc 148
  · exact hroot.hOcc 196
  · exact hroot.hOcc 202
  · exact hroot.hOcc 218
  · exact hroot.hOcc 234
  · exact hroot.hOcc 238
  · exact hroot.hOcc 283
  · exact hroot.hOcc 291
  · exact hroot.hOcc 298
  · exact hroot.hOcc 302
  · exact hroot.hOcc 303
  · exact hroot.hOcc 314
  · exact hroot.hOcc 320
  · exact hroot.hOcc 333
  · exact hroot.hOcc 342
  · exact hroot.hOcc 364
  · exact hroot.hOcc 385
  · exact hroot.hOcc 447
  · exact hroot.hOcc 449
  · exact hroot.hOcc 503
  · exact hroot.hOcc 522
  · exact hroot.hOcc 548
  · exact hroot.hOcc 566
  · exact hroot.hOcc 603
  · exact hroot.hOcc 617
  · exact hroot.hOcc 703
  · exact hroot.hOcc 710
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10
  · change (∑ k, (if k = (27 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27

end QiushiMatmul
