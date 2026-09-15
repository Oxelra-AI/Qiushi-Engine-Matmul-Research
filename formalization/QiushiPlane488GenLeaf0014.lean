import QiushiPlane488GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane488GenLeaf0014Refs : Fin 42 → RowRef 413 41 := ![.occ 90, .occ 115, .occ 116, .occ 127, .occ 129, .occ 140, .occ 141, .occ 153, .occ 155, .occ 156, .occ 162, .occ 171, .occ 173, .occ 186, .occ 192, .occ 195, .occ 201, .occ 210, .occ 215, .occ 216, .occ 241, .occ 259, .occ 265, .occ 268, .occ 275, .occ 298, .occ 300, .occ 349, .occ 374, .occ 376, .occ 395, .occ 408, .sumGe, .nonneg 7, .nonneg 11, .branchLe 27 (0), .branchLe 15 (0), .branchLe 20 (0), .branchGe 25 (1), .branchGe 1 (1), .branchGe 6 (1), .branchGe 21 (1)]

def plane488GenLeaf0014Mult : Fin 42 → Nat := ![29, 205, 222, 72, 20, 267, 93, 26, 29, 64, 231, 254, 130, 79, 192, 115, 260, 116, 122, 115, 214, 102, 258, 202, 346, 30, 66, 16, 239, 103, 139, 143, 615, 123, 442, 291, 551, 130, 1402, 843, 1305, 1233]

theorem plane488GenLeaf0014 (x : Fin 41 → Int)
    (hroot : plane488GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane488GenLeaf0014Refs i).resolveCoeff plane488GenOccSys j)
    (fun i => (plane488GenLeaf0014Refs i).resolveRhs plane488GenOccSys) plane488GenLeaf0014Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane488GenLeaf0014Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 90
  · exact hroot.hOcc 115
  · exact hroot.hOcc 116
  · exact hroot.hOcc 127
  · exact hroot.hOcc 129
  · exact hroot.hOcc 140
  · exact hroot.hOcc 141
  · exact hroot.hOcc 153
  · exact hroot.hOcc 155
  · exact hroot.hOcc 156
  · exact hroot.hOcc 162
  · exact hroot.hOcc 171
  · exact hroot.hOcc 173
  · exact hroot.hOcc 186
  · exact hroot.hOcc 192
  · exact hroot.hOcc 195
  · exact hroot.hOcc 201
  · exact hroot.hOcc 210
  · exact hroot.hOcc 215
  · exact hroot.hOcc 216
  · exact hroot.hOcc 241
  · exact hroot.hOcc 259
  · exact hroot.hOcc 265
  · exact hroot.hOcc 268
  · exact hroot.hOcc 275
  · exact hroot.hOcc 298
  · exact hroot.hOcc 300
  · exact hroot.hOcc 349
  · exact hroot.hOcc 374
  · exact hroot.hOcc 376
  · exact hroot.hOcc 395
  · exact hroot.hOcc 408
  · change (∑ j, (-1 : Int) * x j) ≤ -plane488GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (11 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (27 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (15 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (20 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (25 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25
  · change (∑ k, (if k = (1 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (6 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (21 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21

end QiushiMatmul
