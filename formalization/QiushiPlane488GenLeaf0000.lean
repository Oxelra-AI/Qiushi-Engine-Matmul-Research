import QiushiPlane488GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane488GenLeaf0000Refs : Fin 42 → RowRef 413 41 := ![.occ 88, .occ 90, .occ 98, .occ 100, .occ 101, .occ 104, .occ 108, .occ 112, .occ 117, .occ 135, .occ 148, .occ 149, .occ 152, .occ 159, .occ 197, .occ 205, .occ 229, .occ 252, .occ 259, .occ 265, .occ 291, .occ 305, .occ 309, .occ 344, .occ 362, .occ 370, .occ 374, .occ 379, .occ 384, .occ 395, .occ 404, .sumGe, .branchLe 27 (0), .branchLe 15 (0), .branchLe 20 (0), .branchLe 25 (0), .branchLe 13 (0), .branchLe 24 (0), .branchLe 16 (0), .branchLe 4 (0), .branchLe 37 (0), .branchLe 5 (0)]

def plane488GenLeaf0000Mult : Fin 42 → Nat := ![131, 219, 84, 284, 80, 357, 100, 6, 84, 82, 126, 120, 155, 163, 175, 40, 171, 63, 103, 76, 7, 106, 133, 34, 29, 2, 76, 66, 5, 145, 84, 544, 544, 544, 315, 429, 376, 333, 397, 504, 544, 296]

theorem plane488GenLeaf0000 (x : Fin 41 → Int)
    (hroot : plane488GenOccSys.RootHolds x)
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane488GenLeaf0000Refs i).resolveCoeff plane488GenOccSys j)
    (fun i => (plane488GenLeaf0000Refs i).resolveRhs plane488GenOccSys) plane488GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane488GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 88
  · exact hroot.hOcc 90
  · exact hroot.hOcc 98
  · exact hroot.hOcc 100
  · exact hroot.hOcc 101
  · exact hroot.hOcc 104
  · exact hroot.hOcc 108
  · exact hroot.hOcc 112
  · exact hroot.hOcc 117
  · exact hroot.hOcc 135
  · exact hroot.hOcc 148
  · exact hroot.hOcc 149
  · exact hroot.hOcc 152
  · exact hroot.hOcc 159
  · exact hroot.hOcc 197
  · exact hroot.hOcc 205
  · exact hroot.hOcc 229
  · exact hroot.hOcc 252
  · exact hroot.hOcc 259
  · exact hroot.hOcc 265
  · exact hroot.hOcc 291
  · exact hroot.hOcc 305
  · exact hroot.hOcc 309
  · exact hroot.hOcc 344
  · exact hroot.hOcc 362
  · exact hroot.hOcc 370
  · exact hroot.hOcc 374
  · exact hroot.hOcc 379
  · exact hroot.hOcc 384
  · exact hroot.hOcc 395
  · exact hroot.hOcc 404
  · change (∑ j, (-1 : Int) * x j) ≤ -plane488GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (27 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (15 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (20 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (25 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (13 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (24 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (16 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (4 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (37 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (5 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5

end QiushiMatmul
