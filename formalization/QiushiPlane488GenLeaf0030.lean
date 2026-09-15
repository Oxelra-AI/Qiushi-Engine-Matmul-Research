import QiushiPlane488GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane488GenLeaf0030Refs : Fin 42 → RowRef 413 41 := ![.occ 91, .occ 98, .occ 105, .occ 112, .occ 121, .occ 123, .occ 138, .occ 148, .occ 150, .occ 151, .occ 159, .occ 160, .occ 174, .occ 175, .occ 178, .occ 189, .occ 190, .occ 196, .occ 201, .occ 203, .occ 219, .occ 225, .occ 226, .occ 231, .occ 233, .occ 265, .occ 285, .occ 300, .occ 305, .occ 316, .occ 347, .occ 351, .occ 354, .occ 372, .occ 374, .occ 397, .sumGe, .nonneg 7, .nonneg 8, .branchGe 27 (1), .branchGe 19 (1), .branchLe 38 (0)]

def plane488GenLeaf0030Mult : Fin 42 → Nat := ![108, 335, 13, 104, 226, 31, 237, 118, 56, 2, 60, 136, 34, 404, 157, 76, 139, 181, 52, 231, 411, 215, 11, 326, 29, 105, 26, 13, 45, 223, 45, 25, 154, 56, 134, 87, 648, 480, 105, 1695, 1484, 561]

theorem plane488GenLeaf0030 (x : Fin 41 → Int)
    (hroot : plane488GenOccSys.RootHolds x)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hUB_38 : x 38 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane488GenLeaf0030Refs i).resolveCoeff plane488GenOccSys j)
    (fun i => (plane488GenLeaf0030Refs i).resolveRhs plane488GenOccSys) plane488GenLeaf0030Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane488GenLeaf0030Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 91
  · exact hroot.hOcc 98
  · exact hroot.hOcc 105
  · exact hroot.hOcc 112
  · exact hroot.hOcc 121
  · exact hroot.hOcc 123
  · exact hroot.hOcc 138
  · exact hroot.hOcc 148
  · exact hroot.hOcc 150
  · exact hroot.hOcc 151
  · exact hroot.hOcc 159
  · exact hroot.hOcc 160
  · exact hroot.hOcc 174
  · exact hroot.hOcc 175
  · exact hroot.hOcc 178
  · exact hroot.hOcc 189
  · exact hroot.hOcc 190
  · exact hroot.hOcc 196
  · exact hroot.hOcc 201
  · exact hroot.hOcc 203
  · exact hroot.hOcc 219
  · exact hroot.hOcc 225
  · exact hroot.hOcc 226
  · exact hroot.hOcc 231
  · exact hroot.hOcc 233
  · exact hroot.hOcc 265
  · exact hroot.hOcc 285
  · exact hroot.hOcc 300
  · exact hroot.hOcc 305
  · exact hroot.hOcc 316
  · exact hroot.hOcc 347
  · exact hroot.hOcc 351
  · exact hroot.hOcc 354
  · exact hroot.hOcc 372
  · exact hroot.hOcc 374
  · exact hroot.hOcc 397
  · change (∑ j, (-1 : Int) * x j) ≤ -plane488GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (8 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (27 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (19 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (38 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38

end QiushiMatmul
