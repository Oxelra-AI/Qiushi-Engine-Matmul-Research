import QiushiPlane488GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane488GenLeaf0025Refs : Fin 42 → RowRef 413 41 := ![.occ 105, .occ 109, .occ 112, .occ 115, .occ 130, .occ 136, .occ 148, .occ 153, .occ 165, .occ 175, .occ 183, .occ 190, .occ 195, .occ 224, .occ 226, .occ 231, .occ 242, .occ 254, .occ 263, .occ 267, .occ 268, .occ 272, .occ 278, .occ 303, .occ 310, .occ 324, .occ 346, .occ 347, .occ 357, .occ 366, .occ 405, .sumGe, .nonneg 0, .nonneg 7, .nonneg 17, .branchGe 27 (1), .branchLe 19 (0), .branchLe 16 (0), .branchLe 22 (0), .branchGe 40 (1), .branchLe 35 (0), .branchGe 6 (1)]

def plane488GenLeaf0025Mult : Fin 42 → Nat := ![114, 70, 76, 88, 64, 144, 83, 9, 42, 114, 15, 25, 3, 7, 15, 53, 19, 3, 10, 140, 109, 2, 136, 45, 14, 16, 35, 22, 22, 70, 31, 184, 22, 38, 5, 552, 162, 117, 109, 443, 184, 645]

theorem plane488GenLeaf0025 (x : Fin 41 → Int)
    (hroot : plane488GenOccSys.RootHolds x)
    (hLB_40 : (1 : Int) ≤ x 40)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hUB_35 : x 35 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane488GenLeaf0025Refs i).resolveCoeff plane488GenOccSys j)
    (fun i => (plane488GenLeaf0025Refs i).resolveRhs plane488GenOccSys) plane488GenLeaf0025Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane488GenLeaf0025Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 105
  · exact hroot.hOcc 109
  · exact hroot.hOcc 112
  · exact hroot.hOcc 115
  · exact hroot.hOcc 130
  · exact hroot.hOcc 136
  · exact hroot.hOcc 148
  · exact hroot.hOcc 153
  · exact hroot.hOcc 165
  · exact hroot.hOcc 175
  · exact hroot.hOcc 183
  · exact hroot.hOcc 190
  · exact hroot.hOcc 195
  · exact hroot.hOcc 224
  · exact hroot.hOcc 226
  · exact hroot.hOcc 231
  · exact hroot.hOcc 242
  · exact hroot.hOcc 254
  · exact hroot.hOcc 263
  · exact hroot.hOcc 267
  · exact hroot.hOcc 268
  · exact hroot.hOcc 272
  · exact hroot.hOcc 278
  · exact hroot.hOcc 303
  · exact hroot.hOcc 310
  · exact hroot.hOcc 324
  · exact hroot.hOcc 346
  · exact hroot.hOcc 347
  · exact hroot.hOcc 357
  · exact hroot.hOcc 366
  · exact hroot.hOcc 405
  · change (∑ j, (-1 : Int) * x j) ≤ -plane488GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (7 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (17 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (27 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (19 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (16 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (22 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (40 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_40
  · change (∑ k, (if k = (35 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (6 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6

end QiushiMatmul
