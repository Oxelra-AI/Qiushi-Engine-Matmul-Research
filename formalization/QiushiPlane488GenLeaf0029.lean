import QiushiPlane488GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane488GenLeaf0029Refs : Fin 42 → RowRef 413 41 := ![.occ 91, .occ 105, .occ 112, .occ 128, .occ 145, .occ 151, .occ 156, .occ 162, .occ 175, .occ 184, .occ 206, .occ 210, .occ 214, .occ 219, .occ 222, .occ 223, .occ 224, .occ 226, .occ 232, .occ 243, .occ 254, .occ 258, .occ 278, .occ 300, .occ 313, .occ 323, .occ 330, .occ 334, .occ 342, .occ 349, .occ 355, .occ 364, .occ 380, .occ 395, .occ 404, .sumGe, .nonneg 13, .nonneg 33, .branchGe 27 (1), .branchLe 19 (0), .branchGe 16 (1), .branchGe 39 (1)]

def plane488GenLeaf0029Mult : Fin 42 → Nat := ![5407, 740, 278, 6811, 2413, 6767, 6171, 2892, 2321, 1374, 1657, 1707, 5000, 6015, 4814, 5383, 3263, 2312, 4604, 2146, 6583, 758, 2908, 4667, 2676, 1874, 220, 2301, 1659, 1343, 364, 357, 1556, 447, 1451, 13845, 573, 2242, 25324, 740, 34878, 37406]

theorem plane488GenLeaf0029 (x : Fin 41 → Int)
    (hroot : plane488GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hUB_19 : x 19 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane488GenLeaf0029Refs i).resolveCoeff plane488GenOccSys j)
    (fun i => (plane488GenLeaf0029Refs i).resolveRhs plane488GenOccSys) plane488GenLeaf0029Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane488GenLeaf0029Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 91
  · exact hroot.hOcc 105
  · exact hroot.hOcc 112
  · exact hroot.hOcc 128
  · exact hroot.hOcc 145
  · exact hroot.hOcc 151
  · exact hroot.hOcc 156
  · exact hroot.hOcc 162
  · exact hroot.hOcc 175
  · exact hroot.hOcc 184
  · exact hroot.hOcc 206
  · exact hroot.hOcc 210
  · exact hroot.hOcc 214
  · exact hroot.hOcc 219
  · exact hroot.hOcc 222
  · exact hroot.hOcc 223
  · exact hroot.hOcc 224
  · exact hroot.hOcc 226
  · exact hroot.hOcc 232
  · exact hroot.hOcc 243
  · exact hroot.hOcc 254
  · exact hroot.hOcc 258
  · exact hroot.hOcc 278
  · exact hroot.hOcc 300
  · exact hroot.hOcc 313
  · exact hroot.hOcc 323
  · exact hroot.hOcc 330
  · exact hroot.hOcc 334
  · exact hroot.hOcc 342
  · exact hroot.hOcc 349
  · exact hroot.hOcc 355
  · exact hroot.hOcc 364
  · exact hroot.hOcc 380
  · exact hroot.hOcc 395
  · exact hroot.hOcc 404
  · change (∑ j, (-1 : Int) * x j) ≤ -plane488GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (13 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (33 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (27 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (19 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (16 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (39 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39

end QiushiMatmul
