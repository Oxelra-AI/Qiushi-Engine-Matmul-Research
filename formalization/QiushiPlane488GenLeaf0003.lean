import QiushiPlane488GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane488GenLeaf0003Refs : Fin 41 → RowRef 413 41 := ![.occ 91, .occ 96, .occ 104, .occ 114, .occ 116, .occ 130, .occ 133, .occ 150, .occ 154, .occ 155, .occ 190, .occ 191, .occ 193, .occ 199, .occ 217, .occ 225, .occ 229, .occ 252, .occ 259, .occ 265, .occ 272, .occ 279, .occ 294, .occ 302, .occ 309, .occ 322, .occ 355, .occ 364, .occ 368, .occ 376, .occ 397, .occ 401, .sumGe, .branchLe 27 (0), .branchLe 15 (0), .branchLe 20 (0), .branchLe 25 (0), .branchLe 13 (0), .branchLe 24 (0), .branchLe 16 (0), .branchGe 4 (1)]

def plane488GenLeaf0003Mult : Fin 41 → Nat := ![443, 653, 254, 157, 324, 667, 117, 347, 242, 515, 468, 195, 120, 274, 177, 418, 144, 46, 162, 170, 113, 85, 104, 11, 392, 109, 9, 162, 49, 83, 18, 190, 1030, 1003, 1012, 1019, 842, 632, 612, 1021, 3194]

theorem plane488GenLeaf0003 (x : Fin 41 → Int)
    (hroot : plane488GenOccSys.RootHolds x)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane488GenLeaf0003Refs i).resolveCoeff plane488GenOccSys j)
    (fun i => (plane488GenLeaf0003Refs i).resolveRhs plane488GenOccSys) plane488GenLeaf0003Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane488GenLeaf0003Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 91
  · exact hroot.hOcc 96
  · exact hroot.hOcc 104
  · exact hroot.hOcc 114
  · exact hroot.hOcc 116
  · exact hroot.hOcc 130
  · exact hroot.hOcc 133
  · exact hroot.hOcc 150
  · exact hroot.hOcc 154
  · exact hroot.hOcc 155
  · exact hroot.hOcc 190
  · exact hroot.hOcc 191
  · exact hroot.hOcc 193
  · exact hroot.hOcc 199
  · exact hroot.hOcc 217
  · exact hroot.hOcc 225
  · exact hroot.hOcc 229
  · exact hroot.hOcc 252
  · exact hroot.hOcc 259
  · exact hroot.hOcc 265
  · exact hroot.hOcc 272
  · exact hroot.hOcc 279
  · exact hroot.hOcc 294
  · exact hroot.hOcc 302
  · exact hroot.hOcc 309
  · exact hroot.hOcc 322
  · exact hroot.hOcc 355
  · exact hroot.hOcc 364
  · exact hroot.hOcc 368
  · exact hroot.hOcc 376
  · exact hroot.hOcc 397
  · exact hroot.hOcc 401
  · change (∑ j, (-1 : Int) * x j) ≤ -plane488GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (27 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (15 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (20 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (25 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (13 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (24 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (16 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (4 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4

end QiushiMatmul
