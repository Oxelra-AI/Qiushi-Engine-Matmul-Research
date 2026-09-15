import QiushiPlane485GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane485GenLeaf0024Refs : Fin 42 → RowRef 421 41 := ![.occ 103, .occ 131, .occ 134, .occ 136, .occ 140, .occ 146, .occ 147, .occ 148, .occ 150, .occ 154, .occ 155, .occ 162, .occ 166, .occ 177, .occ 184, .occ 195, .occ 210, .occ 213, .occ 218, .occ 221, .occ 228, .occ 266, .occ 282, .occ 330, .occ 335, .occ 346, .occ 352, .occ 353, .occ 372, .occ 377, .occ 401, .occ 414, .occ 416, .sumGe, .nonneg 0, .nonneg 4, .branchLe 28 (0), .branchGe 21 (1), .branchLe 32 (0), .branchLe 25 (0), .branchGe 23 (1), .branchGe 9 (1)]

def plane485GenLeaf0024Mult : Fin 42 → Nat := ![12616, 20732, 45452, 36744, 24452, 42334, 17099, 2000, 40878, 25454, 1136, 8070, 108764, 104562, 17420, 39458, 27110, 5240, 29692, 11254, 28148, 7036, 8963, 23991, 39554, 6359, 21001, 21965, 30092, 172, 13719, 2658, 10905, 136912, 60204, 18686, 104390, 346103, 102016, 70248, 84605, 243676]

theorem plane485GenLeaf0024 (x : Fin 41 → Int)
    (hroot : plane485GenOccSys.RootHolds x)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane485GenLeaf0024Refs i).resolveCoeff plane485GenOccSys j)
    (fun i => (plane485GenLeaf0024Refs i).resolveRhs plane485GenOccSys) plane485GenLeaf0024Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane485GenLeaf0024Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 103
  · exact hroot.hOcc 131
  · exact hroot.hOcc 134
  · exact hroot.hOcc 136
  · exact hroot.hOcc 140
  · exact hroot.hOcc 146
  · exact hroot.hOcc 147
  · exact hroot.hOcc 148
  · exact hroot.hOcc 150
  · exact hroot.hOcc 154
  · exact hroot.hOcc 155
  · exact hroot.hOcc 162
  · exact hroot.hOcc 166
  · exact hroot.hOcc 177
  · exact hroot.hOcc 184
  · exact hroot.hOcc 195
  · exact hroot.hOcc 210
  · exact hroot.hOcc 213
  · exact hroot.hOcc 218
  · exact hroot.hOcc 221
  · exact hroot.hOcc 228
  · exact hroot.hOcc 266
  · exact hroot.hOcc 282
  · exact hroot.hOcc 330
  · exact hroot.hOcc 335
  · exact hroot.hOcc 346
  · exact hroot.hOcc 352
  · exact hroot.hOcc 353
  · exact hroot.hOcc 372
  · exact hroot.hOcc 377
  · exact hroot.hOcc 401
  · exact hroot.hOcc 414
  · exact hroot.hOcc 416
  · change (∑ j, (-1 : Int) * x j) ≤ -plane485GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (4 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (28 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (21 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21
  · change (∑ k, (if k = (32 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (25 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (23 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (9 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9

end QiushiMatmul
