import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0020Refs : Fin 44 → RowRef 713 43 := ![.occ 86, .occ 94, .occ 95, .occ 104, .occ 106, .occ 110, .occ 112, .occ 146, .occ 229, .occ 239, .occ 271, .occ 282, .occ 283, .occ 291, .occ 309, .occ 335, .occ 338, .occ 354, .occ 387, .occ 388, .occ 397, .occ 474, .occ 489, .occ 494, .occ 500, .occ 501, .occ 549, .occ 581, .occ 599, .occ 613, .occ 649, .occ 692, .occ 704, .occ 709, .sumGe, .branchLe 29 (0), .branchLe 4 (0), .branchLe 23 (0), .branchGe 16 (1), .branchGe 15 (1), .branchLe 32 (0), .branchLe 3 (0), .branchLe 42 (0), .branchGe 20 (1)]

def plane490GenLeaf0020Mult : Fin 44 → Nat := ![22662, 28518, 26506, 40321, 18485, 24588, 2708, 10992, 3112, 9510, 4370, 1254, 4633, 442, 9279, 1491, 7750, 3139, 2975, 14817, 7905, 2400, 1372, 10651, 9051, 203, 7935, 1518, 3093, 5910, 17252, 10954, 6113, 1152, 40321, 36566, 30443, 39169, 75161, 14342, 26640, 15319, 35485, 122203]

theorem plane490GenLeaf0020 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0020Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0020Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0020Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0020Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 86
  · exact hroot.hOcc 94
  · exact hroot.hOcc 95
  · exact hroot.hOcc 104
  · exact hroot.hOcc 106
  · exact hroot.hOcc 110
  · exact hroot.hOcc 112
  · exact hroot.hOcc 146
  · exact hroot.hOcc 229
  · exact hroot.hOcc 239
  · exact hroot.hOcc 271
  · exact hroot.hOcc 282
  · exact hroot.hOcc 283
  · exact hroot.hOcc 291
  · exact hroot.hOcc 309
  · exact hroot.hOcc 335
  · exact hroot.hOcc 338
  · exact hroot.hOcc 354
  · exact hroot.hOcc 387
  · exact hroot.hOcc 388
  · exact hroot.hOcc 397
  · exact hroot.hOcc 474
  · exact hroot.hOcc 489
  · exact hroot.hOcc 494
  · exact hroot.hOcc 500
  · exact hroot.hOcc 501
  · exact hroot.hOcc 549
  · exact hroot.hOcc 581
  · exact hroot.hOcc 599
  · exact hroot.hOcc 613
  · exact hroot.hOcc 649
  · exact hroot.hOcc 692
  · exact hroot.hOcc 704
  · exact hroot.hOcc 709
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20

end QiushiMatmul
