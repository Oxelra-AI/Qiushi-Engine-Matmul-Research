import QiushiPlane488GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane488GenLeaf0027Refs : Fin 42 → RowRef 413 41 := ![.occ 96, .occ 104, .occ 105, .occ 109, .occ 114, .occ 123, .occ 145, .occ 167, .occ 175, .occ 179, .occ 180, .occ 183, .occ 190, .occ 206, .occ 225, .occ 226, .occ 231, .occ 232, .occ 246, .occ 269, .occ 270, .occ 271, .occ 272, .occ 278, .occ 288, .occ 293, .occ 300, .occ 301, .occ 336, .occ 342, .occ 360, .occ 364, .occ 372, .occ 382, .occ 389, .occ 397, .sumGe, .nonneg 7, .branchGe 27 (1), .branchLe 19 (0), .branchLe 16 (0), .branchGe 22 (1)]

def plane488GenLeaf0027Mult : Fin 42 → Nat := ![21164, 26967, 67953, 30661, 360, 22847, 36811, 8937, 5638, 8351, 19452, 1652, 22427, 19872, 9636, 13710, 35558, 1525, 23786, 2898, 12018, 23532, 6771, 1271, 22008, 9512, 6865, 12495, 19886, 7998, 2294, 17433, 4440, 7053, 7081, 5428, 67953, 5071, 129659, 62525, 47068, 254736]

theorem plane488GenLeaf0027 (x : Fin 41 → Int)
    (hroot : plane488GenOccSys.RootHolds x)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane488GenLeaf0027Refs i).resolveCoeff plane488GenOccSys j)
    (fun i => (plane488GenLeaf0027Refs i).resolveRhs plane488GenOccSys) plane488GenLeaf0027Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane488GenLeaf0027Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 96
  · exact hroot.hOcc 104
  · exact hroot.hOcc 105
  · exact hroot.hOcc 109
  · exact hroot.hOcc 114
  · exact hroot.hOcc 123
  · exact hroot.hOcc 145
  · exact hroot.hOcc 167
  · exact hroot.hOcc 175
  · exact hroot.hOcc 179
  · exact hroot.hOcc 180
  · exact hroot.hOcc 183
  · exact hroot.hOcc 190
  · exact hroot.hOcc 206
  · exact hroot.hOcc 225
  · exact hroot.hOcc 226
  · exact hroot.hOcc 231
  · exact hroot.hOcc 232
  · exact hroot.hOcc 246
  · exact hroot.hOcc 269
  · exact hroot.hOcc 270
  · exact hroot.hOcc 271
  · exact hroot.hOcc 272
  · exact hroot.hOcc 278
  · exact hroot.hOcc 288
  · exact hroot.hOcc 293
  · exact hroot.hOcc 300
  · exact hroot.hOcc 301
  · exact hroot.hOcc 336
  · exact hroot.hOcc 342
  · exact hroot.hOcc 360
  · exact hroot.hOcc 364
  · exact hroot.hOcc 372
  · exact hroot.hOcc 382
  · exact hroot.hOcc 389
  · exact hroot.hOcc 397
  · change (∑ j, (-1 : Int) * x j) ≤ -plane488GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (27 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (19 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (16 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (22 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22

end QiushiMatmul
