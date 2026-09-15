import QiushiPlane488GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane488GenLeaf0006Refs : Fin 41 → RowRef 413 41 := ![.occ 87, .occ 91, .occ 96, .occ 102, .occ 109, .occ 125, .occ 149, .occ 152, .occ 153, .occ 159, .occ 167, .occ 175, .occ 190, .occ 192, .occ 198, .occ 202, .occ 210, .occ 212, .occ 224, .occ 232, .occ 237, .occ 252, .occ 286, .occ 309, .occ 328, .occ 361, .occ 365, .occ 373, .occ 381, .occ 395, .occ 396, .occ 398, .sumGe, .nonneg 8, .branchLe 27 (0), .branchLe 15 (0), .branchLe 20 (0), .branchLe 25 (0), .branchLe 13 (0), .branchGe 24 (1), .branchGe 23 (1)]

def plane488GenLeaf0006Mult : Fin 41 → Nat := ![147, 16, 53, 43, 70, 115, 130, 6, 11, 9, 72, 56, 64, 56, 56, 9, 72, 105, 86, 46, 38, 94, 33, 40, 14, 3, 13, 8, 81, 70, 3, 4, 223, 9, 164, 220, 107, 138, 70, 519, 451]

theorem plane488GenLeaf0006 (x : Fin 41 → Int)
    (hroot : plane488GenOccSys.RootHolds x)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane488GenLeaf0006Refs i).resolveCoeff plane488GenOccSys j)
    (fun i => (plane488GenLeaf0006Refs i).resolveRhs plane488GenOccSys) plane488GenLeaf0006Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane488GenLeaf0006Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 91
  · exact hroot.hOcc 96
  · exact hroot.hOcc 102
  · exact hroot.hOcc 109
  · exact hroot.hOcc 125
  · exact hroot.hOcc 149
  · exact hroot.hOcc 152
  · exact hroot.hOcc 153
  · exact hroot.hOcc 159
  · exact hroot.hOcc 167
  · exact hroot.hOcc 175
  · exact hroot.hOcc 190
  · exact hroot.hOcc 192
  · exact hroot.hOcc 198
  · exact hroot.hOcc 202
  · exact hroot.hOcc 210
  · exact hroot.hOcc 212
  · exact hroot.hOcc 224
  · exact hroot.hOcc 232
  · exact hroot.hOcc 237
  · exact hroot.hOcc 252
  · exact hroot.hOcc 286
  · exact hroot.hOcc 309
  · exact hroot.hOcc 328
  · exact hroot.hOcc 361
  · exact hroot.hOcc 365
  · exact hroot.hOcc 373
  · exact hroot.hOcc 381
  · exact hroot.hOcc 395
  · exact hroot.hOcc 396
  · exact hroot.hOcc 398
  · change (∑ j, (-1 : Int) * x j) ≤ -plane488GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (27 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (15 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (20 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (25 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (13 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (24 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24
  · change (∑ k, (if k = (23 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23

end QiushiMatmul
