import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0020Refs : Fin 49 → RowRef 668 48 := ![.occ 103, .occ 110, .occ 111, .occ 118, .occ 120, .occ 123, .occ 181, .occ 186, .occ 217, .occ 227, .occ 231, .occ 235, .occ 253, .occ 263, .occ 269, .occ 279, .occ 294, .occ 295, .occ 296, .occ 303, .occ 308, .occ 313, .occ 322, .occ 334, .occ 369, .occ 377, .occ 378, .occ 386, .occ 404, .occ 415, .occ 442, .occ 468, .occ 474, .occ 500, .occ 615, .occ 625, .occ 648, .occ 651, .occ 656, .occ 658, .sumGe, .nonneg 0, .branchLe 39 (0), .branchLe 23 (0), .branchGe 6 (1), .branchLe 33 (0), .branchLe 14 (0), .branchLe 29 (0), .branchLe 9 (0)]

def plane487GenLeaf0020Mult : Fin 49 → Nat := ![24116, 139771, 17546, 40107, 28184, 25370, 10151, 100033, 3645, 14923, 53931, 20885, 76525, 15545, 67136, 6499, 74317, 99735, 115778, 41040, 372, 2123, 8424, 15586, 12931, 5310, 55899, 113084, 95077, 49006, 23033, 23478, 12664, 6258, 1443, 3312, 73540, 5856, 25973, 7771, 241486, 110676, 241486, 229131, 667234, 84190, 174101, 141655, 241486]

theorem plane487GenLeaf0020 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0020Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0020Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0020Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0020Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 103
  · exact hroot.hOcc 110
  · exact hroot.hOcc 111
  · exact hroot.hOcc 118
  · exact hroot.hOcc 120
  · exact hroot.hOcc 123
  · exact hroot.hOcc 181
  · exact hroot.hOcc 186
  · exact hroot.hOcc 217
  · exact hroot.hOcc 227
  · exact hroot.hOcc 231
  · exact hroot.hOcc 235
  · exact hroot.hOcc 253
  · exact hroot.hOcc 263
  · exact hroot.hOcc 269
  · exact hroot.hOcc 279
  · exact hroot.hOcc 294
  · exact hroot.hOcc 295
  · exact hroot.hOcc 296
  · exact hroot.hOcc 303
  · exact hroot.hOcc 308
  · exact hroot.hOcc 313
  · exact hroot.hOcc 322
  · exact hroot.hOcc 334
  · exact hroot.hOcc 369
  · exact hroot.hOcc 377
  · exact hroot.hOcc 378
  · exact hroot.hOcc 386
  · exact hroot.hOcc 404
  · exact hroot.hOcc 415
  · exact hroot.hOcc 442
  · exact hroot.hOcc 468
  · exact hroot.hOcc 474
  · exact hroot.hOcc 500
  · exact hroot.hOcc 615
  · exact hroot.hOcc 625
  · exact hroot.hOcc 648
  · exact hroot.hOcc 651
  · exact hroot.hOcc 656
  · exact hroot.hOcc 658
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (6 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (33 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (14 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (29 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (9 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9

end QiushiMatmul
