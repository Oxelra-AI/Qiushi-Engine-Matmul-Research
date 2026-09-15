import QiushiPlane488GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane488GenLeaf0017Refs : Fin 41 → RowRef 413 41 := ![.occ 89, .occ 90, .occ 96, .occ 107, .occ 109, .occ 114, .occ 116, .occ 124, .occ 156, .occ 164, .occ 165, .occ 170, .occ 174, .occ 186, .occ 187, .occ 213, .occ 214, .occ 219, .occ 221, .occ 232, .occ 243, .occ 253, .occ 272, .occ 278, .occ 299, .occ 308, .occ 323, .occ 366, .occ 372, .occ 387, .occ 392, .occ 395, .occ 401, .occ 404, .occ 407, .sumGe, .nonneg 7, .branchLe 27 (0), .branchLe 15 (0), .branchGe 20 (1), .branchGe 39 (1)]

def plane488GenLeaf0017Mult : Fin 41 → Nat := ![1058, 3144, 1944, 3835, 8147, 347, 2434, 2063, 1784, 661, 4796, 7320, 5919, 785, 2051, 19403, 1330, 4711, 8197, 347, 8060, 3828, 2888, 10175, 2131, 5430, 1558, 347, 2181, 1572, 4052, 5475, 1330, 1362, 3059, 21080, 2888, 6308, 11526, 65130, 60643]

theorem plane488GenLeaf0017 (x : Fin 41 → Int)
    (hroot : plane488GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane488GenLeaf0017Refs i).resolveCoeff plane488GenOccSys j)
    (fun i => (plane488GenLeaf0017Refs i).resolveRhs plane488GenOccSys) plane488GenLeaf0017Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane488GenLeaf0017Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 89
  · exact hroot.hOcc 90
  · exact hroot.hOcc 96
  · exact hroot.hOcc 107
  · exact hroot.hOcc 109
  · exact hroot.hOcc 114
  · exact hroot.hOcc 116
  · exact hroot.hOcc 124
  · exact hroot.hOcc 156
  · exact hroot.hOcc 164
  · exact hroot.hOcc 165
  · exact hroot.hOcc 170
  · exact hroot.hOcc 174
  · exact hroot.hOcc 186
  · exact hroot.hOcc 187
  · exact hroot.hOcc 213
  · exact hroot.hOcc 214
  · exact hroot.hOcc 219
  · exact hroot.hOcc 221
  · exact hroot.hOcc 232
  · exact hroot.hOcc 243
  · exact hroot.hOcc 253
  · exact hroot.hOcc 272
  · exact hroot.hOcc 278
  · exact hroot.hOcc 299
  · exact hroot.hOcc 308
  · exact hroot.hOcc 323
  · exact hroot.hOcc 366
  · exact hroot.hOcc 372
  · exact hroot.hOcc 387
  · exact hroot.hOcc 392
  · exact hroot.hOcc 395
  · exact hroot.hOcc 401
  · exact hroot.hOcc 404
  · exact hroot.hOcc 407
  · change (∑ j, (-1 : Int) * x j) ≤ -plane488GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (27 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (15 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (20 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20
  · change (∑ k, (if k = (39 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39

end QiushiMatmul
