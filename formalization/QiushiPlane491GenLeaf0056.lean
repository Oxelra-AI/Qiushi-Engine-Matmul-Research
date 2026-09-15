import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0056Refs : Fin 50 → RowRef 726 49 := ![.occ 79, .occ 100, .occ 102, .occ 106, .occ 111, .occ 116, .occ 117, .occ 219, .occ 232, .occ 255, .occ 257, .occ 260, .occ 315, .occ 317, .occ 332, .occ 338, .occ 360, .occ 363, .occ 367, .occ 389, .occ 391, .occ 441, .occ 444, .occ 479, .occ 493, .occ 504, .occ 506, .occ 510, .occ 511, .occ 526, .occ 529, .occ 539, .occ 546, .occ 626, .occ 628, .occ 634, .occ 642, .occ 644, .occ 653, .occ 691, .occ 692, .sumGe, .branchLe 31 (0), .branchLe 16 (0), .branchGe 27 (1), .branchLe 11 (0), .branchLe 23 (0), .branchGe 0 (1), .branchGe 39 (1), .branchLe 30 (0)]

def plane491GenLeaf0056Mult : Fin 50 → Nat := ![230174, 158822, 44436, 200947, 7012, 129452, 92630, 11292, 152860, 39770, 23586, 98818, 10809, 26500, 18154, 9341, 61217, 23817, 38697, 70058, 21729, 32190, 21429, 35719, 12476, 19122, 28165, 27729, 27074, 3741, 27905, 36219, 5271, 107553, 54805, 31103, 13567, 106932, 75226, 104233, 126162, 326033, 326033, 185383, 955786, 244728, 115338, 747540, 385952, 285392]

theorem plane491GenLeaf0056 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0056Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0056Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0056Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0056Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 79
  · exact hroot.hOcc 100
  · exact hroot.hOcc 102
  · exact hroot.hOcc 106
  · exact hroot.hOcc 111
  · exact hroot.hOcc 116
  · exact hroot.hOcc 117
  · exact hroot.hOcc 219
  · exact hroot.hOcc 232
  · exact hroot.hOcc 255
  · exact hroot.hOcc 257
  · exact hroot.hOcc 260
  · exact hroot.hOcc 315
  · exact hroot.hOcc 317
  · exact hroot.hOcc 332
  · exact hroot.hOcc 338
  · exact hroot.hOcc 360
  · exact hroot.hOcc 363
  · exact hroot.hOcc 367
  · exact hroot.hOcc 389
  · exact hroot.hOcc 391
  · exact hroot.hOcc 441
  · exact hroot.hOcc 444
  · exact hroot.hOcc 479
  · exact hroot.hOcc 493
  · exact hroot.hOcc 504
  · exact hroot.hOcc 506
  · exact hroot.hOcc 510
  · exact hroot.hOcc 511
  · exact hroot.hOcc 526
  · exact hroot.hOcc 529
  · exact hroot.hOcc 539
  · exact hroot.hOcc 546
  · exact hroot.hOcc 626
  · exact hroot.hOcc 628
  · exact hroot.hOcc 634
  · exact hroot.hOcc 642
  · exact hroot.hOcc 644
  · exact hroot.hOcc 653
  · exact hroot.hOcc 691
  · exact hroot.hOcc 692
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (11 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (23 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (0 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (39 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (30 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30

end QiushiMatmul
