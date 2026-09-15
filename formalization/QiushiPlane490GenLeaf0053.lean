import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0053Refs : Fin 44 → RowRef 713 43 := ![.occ 90, .occ 104, .occ 107, .occ 109, .occ 112, .occ 113, .occ 150, .occ 171, .occ 191, .occ 219, .occ 233, .occ 239, .occ 252, .occ 284, .occ 291, .occ 302, .occ 307, .occ 314, .occ 336, .occ 354, .occ 370, .occ 394, .occ 421, .occ 460, .occ 472, .occ 478, .occ 480, .occ 583, .occ 610, .occ 629, .occ 649, .occ 671, .occ 674, .occ 681, .occ 688, .occ 692, .occ 711, .sumGe, .branchLe 29 (0), .branchLe 4 (0), .branchGe 23 (1), .branchGe 30 (1), .branchLe 6 (0), .branchLe 10 (0)]

def plane490GenLeaf0053Mult : Fin 44 → Nat := ![4496, 8496, 16089, 5986, 6716, 6742, 11878, 13095, 49665, 26797, 4761, 13109, 11690, 8965, 14897, 17011, 16161, 14820, 32366, 919, 8582, 1742, 104, 29345, 4155, 275, 1225, 1646, 25270, 15949, 14388, 406, 6627, 573, 577, 8965, 1225, 58630, 52644, 43156, 169489, 197713, 58630, 41619]

theorem plane490GenLeaf0053 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0053Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0053Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0053Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0053Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 90
  · exact hroot.hOcc 104
  · exact hroot.hOcc 107
  · exact hroot.hOcc 109
  · exact hroot.hOcc 112
  · exact hroot.hOcc 113
  · exact hroot.hOcc 150
  · exact hroot.hOcc 171
  · exact hroot.hOcc 191
  · exact hroot.hOcc 219
  · exact hroot.hOcc 233
  · exact hroot.hOcc 239
  · exact hroot.hOcc 252
  · exact hroot.hOcc 284
  · exact hroot.hOcc 291
  · exact hroot.hOcc 302
  · exact hroot.hOcc 307
  · exact hroot.hOcc 314
  · exact hroot.hOcc 336
  · exact hroot.hOcc 354
  · exact hroot.hOcc 370
  · exact hroot.hOcc 394
  · exact hroot.hOcc 421
  · exact hroot.hOcc 460
  · exact hroot.hOcc 472
  · exact hroot.hOcc 478
  · exact hroot.hOcc 480
  · exact hroot.hOcc 583
  · exact hroot.hOcc 610
  · exact hroot.hOcc 629
  · exact hroot.hOcc 649
  · exact hroot.hOcc 671
  · exact hroot.hOcc 674
  · exact hroot.hOcc 681
  · exact hroot.hOcc 688
  · exact hroot.hOcc 692
  · exact hroot.hOcc 711
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10

end QiushiMatmul
