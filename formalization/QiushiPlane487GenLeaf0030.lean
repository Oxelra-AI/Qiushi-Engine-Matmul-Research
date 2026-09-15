import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0030Refs : Fin 49 → RowRef 668 48 := ![.occ 83, .occ 95, .occ 131, .occ 179, .occ 189, .occ 194, .occ 216, .occ 218, .occ 219, .occ 231, .occ 233, .occ 235, .occ 242, .occ 269, .occ 295, .occ 302, .occ 303, .occ 316, .occ 321, .occ 322, .occ 333, .occ 352, .occ 378, .occ 381, .occ 386, .occ 388, .occ 389, .occ 390, .occ 399, .occ 400, .occ 415, .occ 459, .occ 471, .occ 521, .occ 546, .occ 553, .occ 566, .occ 634, .occ 639, .sumGe, .nonneg 17, .nonneg 30, .nonneg 46, .branchLe 39 (0), .branchLe 23 (0), .branchGe 6 (1), .branchLe 33 (0), .branchGe 14 (1), .branchGe 24 (1)]

def plane487GenLeaf0030Mult : Fin 49 → Nat := ![11342, 11458, 148061, 149777, 79140, 37161, 6204, 183419, 185721, 51895, 94838, 34249, 26285, 50185, 70789, 37944, 183005, 42695, 116386, 21599, 77099, 731, 16594, 26486, 84791, 5567, 83729, 37426, 9828, 34103, 55952, 42401, 28116, 53400, 70480, 5931, 7097, 11458, 73385, 312506, 210312, 25859, 70319, 242026, 312506, 320579, 155099, 822811, 743855]

theorem plane487GenLeaf0030 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0030Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0030Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0030Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0030Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 83
  · exact hroot.hOcc 95
  · exact hroot.hOcc 131
  · exact hroot.hOcc 179
  · exact hroot.hOcc 189
  · exact hroot.hOcc 194
  · exact hroot.hOcc 216
  · exact hroot.hOcc 218
  · exact hroot.hOcc 219
  · exact hroot.hOcc 231
  · exact hroot.hOcc 233
  · exact hroot.hOcc 235
  · exact hroot.hOcc 242
  · exact hroot.hOcc 269
  · exact hroot.hOcc 295
  · exact hroot.hOcc 302
  · exact hroot.hOcc 303
  · exact hroot.hOcc 316
  · exact hroot.hOcc 321
  · exact hroot.hOcc 322
  · exact hroot.hOcc 333
  · exact hroot.hOcc 352
  · exact hroot.hOcc 378
  · exact hroot.hOcc 381
  · exact hroot.hOcc 386
  · exact hroot.hOcc 388
  · exact hroot.hOcc 389
  · exact hroot.hOcc 390
  · exact hroot.hOcc 399
  · exact hroot.hOcc 400
  · exact hroot.hOcc 415
  · exact hroot.hOcc 459
  · exact hroot.hOcc 471
  · exact hroot.hOcc 521
  · exact hroot.hOcc 546
  · exact hroot.hOcc 553
  · exact hroot.hOcc 566
  · exact hroot.hOcc 634
  · exact hroot.hOcc 639
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (17 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (30 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (46 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (6 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (33 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (14 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (24 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24

end QiushiMatmul
