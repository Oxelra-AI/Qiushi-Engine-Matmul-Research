import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0078Refs : Fin 44 → RowRef 713 43 := ![.occ 90, .occ 95, .occ 100, .occ 101, .occ 105, .occ 107, .occ 108, .occ 126, .occ 152, .occ 178, .occ 182, .occ 192, .occ 203, .occ 204, .occ 225, .occ 273, .occ 290, .occ 294, .occ 314, .occ 335, .occ 339, .occ 364, .occ 365, .occ 392, .occ 395, .occ 418, .occ 475, .occ 476, .occ 479, .occ 486, .occ 525, .occ 632, .occ 638, .occ 667, .occ 691, .occ 709, .sumGe, .branchGe 29 (1), .branchLe 18 (0), .branchLe 12 (0), .branchLe 22 (0), .branchLe 1 (0), .branchLe 10 (0), .branchGe 14 (1)]

def plane490GenLeaf0078Mult : Fin 44 → Nat := ![265, 3064, 3635, 1059, 8464, 459, 4798, 5092, 2146, 3819, 1008, 172, 153, 1831, 2222, 2634, 2190, 954, 2015, 909, 2351, 2526, 667, 2324, 444, 3015, 877, 413, 412, 2142, 332, 2599, 750, 1033, 3378, 620, 8796, 26242, 5418, 8176, 3462, 8796, 5271, 27888]

theorem plane490GenLeaf0078 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0078Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0078Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0078Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0078Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 90
  · exact hroot.hOcc 95
  · exact hroot.hOcc 100
  · exact hroot.hOcc 101
  · exact hroot.hOcc 105
  · exact hroot.hOcc 107
  · exact hroot.hOcc 108
  · exact hroot.hOcc 126
  · exact hroot.hOcc 152
  · exact hroot.hOcc 178
  · exact hroot.hOcc 182
  · exact hroot.hOcc 192
  · exact hroot.hOcc 203
  · exact hroot.hOcc 204
  · exact hroot.hOcc 225
  · exact hroot.hOcc 273
  · exact hroot.hOcc 290
  · exact hroot.hOcc 294
  · exact hroot.hOcc 314
  · exact hroot.hOcc 335
  · exact hroot.hOcc 339
  · exact hroot.hOcc 364
  · exact hroot.hOcc 365
  · exact hroot.hOcc 392
  · exact hroot.hOcc 395
  · exact hroot.hOcc 418
  · exact hroot.hOcc 475
  · exact hroot.hOcc 476
  · exact hroot.hOcc 479
  · exact hroot.hOcc 486
  · exact hroot.hOcc 525
  · exact hroot.hOcc 632
  · exact hroot.hOcc 638
  · exact hroot.hOcc 667
  · exact hroot.hOcc 691
  · exact hroot.hOcc 709
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (12 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14

end QiushiMatmul
