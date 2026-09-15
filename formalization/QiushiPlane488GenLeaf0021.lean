import QiushiPlane488GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane488GenLeaf0021Refs : Fin 41 → RowRef 413 41 := ![.occ 100, .occ 104, .occ 110, .occ 112, .occ 118, .occ 124, .occ 153, .occ 156, .occ 159, .occ 161, .occ 174, .occ 183, .occ 184, .occ 190, .occ 201, .occ 210, .occ 219, .occ 224, .occ 225, .occ 249, .occ 251, .occ 272, .occ 282, .occ 288, .occ 292, .occ 328, .occ 330, .occ 333, .occ 339, .occ 352, .occ 353, .occ 385, .occ 395, .occ 400, .sumGe, .nonneg 0, .nonneg 17, .branchLe 27 (0), .branchGe 15 (1), .branchGe 14 (1), .branchLe 28 (0)]

def plane488GenLeaf0021Mult : Fin 41 → Nat := ![66961, 83702, 88990, 102742, 18399, 16036, 181, 74288, 7663, 26824, 21871, 24898, 14208, 54420, 7663, 9312, 40591, 1305, 25534, 13012, 21025, 20104, 42, 19670, 13072, 7640, 1672, 5184, 44309, 13950, 13504, 6539, 28469, 47449, 129581, 64471, 7459, 88990, 238949, 322050, 115373]

theorem plane488GenLeaf0021 (x : Fin 41 → Int)
    (hroot : plane488GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane488GenLeaf0021Refs i).resolveCoeff plane488GenOccSys j)
    (fun i => (plane488GenLeaf0021Refs i).resolveRhs plane488GenOccSys) plane488GenLeaf0021Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane488GenLeaf0021Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 100
  · exact hroot.hOcc 104
  · exact hroot.hOcc 110
  · exact hroot.hOcc 112
  · exact hroot.hOcc 118
  · exact hroot.hOcc 124
  · exact hroot.hOcc 153
  · exact hroot.hOcc 156
  · exact hroot.hOcc 159
  · exact hroot.hOcc 161
  · exact hroot.hOcc 174
  · exact hroot.hOcc 183
  · exact hroot.hOcc 184
  · exact hroot.hOcc 190
  · exact hroot.hOcc 201
  · exact hroot.hOcc 210
  · exact hroot.hOcc 219
  · exact hroot.hOcc 224
  · exact hroot.hOcc 225
  · exact hroot.hOcc 249
  · exact hroot.hOcc 251
  · exact hroot.hOcc 272
  · exact hroot.hOcc 282
  · exact hroot.hOcc 288
  · exact hroot.hOcc 292
  · exact hroot.hOcc 328
  · exact hroot.hOcc 330
  · exact hroot.hOcc 333
  · exact hroot.hOcc 339
  · exact hroot.hOcc 352
  · exact hroot.hOcc 353
  · exact hroot.hOcc 385
  · exact hroot.hOcc 395
  · exact hroot.hOcc 400
  · change (∑ j, (-1 : Int) * x j) ≤ -plane488GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (17 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (27 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (15 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (14 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (28 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28

end QiushiMatmul
