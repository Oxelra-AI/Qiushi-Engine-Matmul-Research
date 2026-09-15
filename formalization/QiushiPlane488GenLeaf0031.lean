import QiushiPlane488GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane488GenLeaf0031Refs : Fin 42 → RowRef 413 41 := ![.occ 87, .occ 98, .occ 105, .occ 112, .occ 121, .occ 123, .occ 128, .occ 138, .occ 150, .occ 164, .occ 175, .occ 183, .occ 196, .occ 203, .occ 210, .occ 219, .occ 223, .occ 228, .occ 229, .occ 231, .occ 233, .occ 272, .occ 280, .occ 281, .occ 300, .occ 305, .occ 307, .occ 329, .occ 332, .occ 352, .occ 357, .occ 360, .occ 379, .occ 394, .occ 395, .sumGe, .nonneg 7, .nonneg 8, .nonneg 11, .branchGe 27 (1), .branchGe 19 (1), .branchGe 38 (1)]

def plane488GenLeaf0031Mult : Fin 42 → Nat := ![10, 157, 32, 5, 208, 36, 23, 166, 30, 47, 186, 65, 104, 44, 215, 36, 275, 15, 28, 92, 36, 68, 70, 201, 60, 36, 64, 23, 51, 25, 178, 114, 40, 37, 32, 379, 7, 42, 82, 1282, 1216, 1042]

theorem plane488GenLeaf0031 (x : Fin 41 → Int)
    (hroot : plane488GenOccSys.RootHolds x)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_27 : (1 : Int) ≤ x 27)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane488GenLeaf0031Refs i).resolveCoeff plane488GenOccSys j)
    (fun i => (plane488GenLeaf0031Refs i).resolveRhs plane488GenOccSys) plane488GenLeaf0031Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane488GenLeaf0031Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 98
  · exact hroot.hOcc 105
  · exact hroot.hOcc 112
  · exact hroot.hOcc 121
  · exact hroot.hOcc 123
  · exact hroot.hOcc 128
  · exact hroot.hOcc 138
  · exact hroot.hOcc 150
  · exact hroot.hOcc 164
  · exact hroot.hOcc 175
  · exact hroot.hOcc 183
  · exact hroot.hOcc 196
  · exact hroot.hOcc 203
  · exact hroot.hOcc 210
  · exact hroot.hOcc 219
  · exact hroot.hOcc 223
  · exact hroot.hOcc 228
  · exact hroot.hOcc 229
  · exact hroot.hOcc 231
  · exact hroot.hOcc 233
  · exact hroot.hOcc 272
  · exact hroot.hOcc 280
  · exact hroot.hOcc 281
  · exact hroot.hOcc 300
  · exact hroot.hOcc 305
  · exact hroot.hOcc 307
  · exact hroot.hOcc 329
  · exact hroot.hOcc 332
  · exact hroot.hOcc 352
  · exact hroot.hOcc 357
  · exact hroot.hOcc 360
  · exact hroot.hOcc 379
  · exact hroot.hOcc 394
  · exact hroot.hOcc 395
  · change (∑ j, (-1 : Int) * x j) ≤ -plane488GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (8 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (11 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (27 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (19 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (38 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38

end QiushiMatmul
