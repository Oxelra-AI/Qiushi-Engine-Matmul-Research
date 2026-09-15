import QiushiPlane486GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane486GenLeaf0010Refs : Fin 42 → RowRef 262 41 := ![.occ 88, .occ 90, .occ 91, .occ 103, .occ 105, .occ 106, .occ 114, .occ 118, .occ 119, .occ 121, .occ 122, .occ 125, .occ 129, .occ 131, .occ 146, .occ 154, .occ 155, .occ 161, .occ 166, .occ 178, .occ 188, .occ 195, .occ 196, .occ 206, .occ 210, .occ 224, .occ 226, .occ 233, .occ 236, .occ 237, .occ 240, .occ 244, .occ 253, .occ 259, .sumGe, .nonneg 0, .nonneg 7, .nonneg 38, .branchGe 22 (1), .branchLe 16 (0), .branchLe 3 (0), .branchGe 10 (1)]

def plane486GenLeaf0010Mult : Fin 42 → Nat := ![5015, 5186, 5975, 4391, 15391, 15828, 7279, 6749, 6827, 4715, 3735, 4278, 7114, 3219, 13034, 9459, 1526, 2689, 10042, 11164, 4112, 1952, 2267, 76, 2713, 4048, 1182, 2159, 1970, 3155, 8389, 466, 10802, 837, 29699, 8703, 2108, 8277, 61769, 26934, 17700, 42395]

theorem plane486GenLeaf0010 (x : Fin 41 → Int)
    (hroot : plane486GenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane486GenLeaf0010Refs i).resolveCoeff plane486GenOccSys j)
    (fun i => (plane486GenLeaf0010Refs i).resolveRhs plane486GenOccSys) plane486GenLeaf0010Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane486GenLeaf0010Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 88
  · exact hroot.hOcc 90
  · exact hroot.hOcc 91
  · exact hroot.hOcc 103
  · exact hroot.hOcc 105
  · exact hroot.hOcc 106
  · exact hroot.hOcc 114
  · exact hroot.hOcc 118
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 125
  · exact hroot.hOcc 129
  · exact hroot.hOcc 131
  · exact hroot.hOcc 146
  · exact hroot.hOcc 154
  · exact hroot.hOcc 155
  · exact hroot.hOcc 161
  · exact hroot.hOcc 166
  · exact hroot.hOcc 178
  · exact hroot.hOcc 188
  · exact hroot.hOcc 195
  · exact hroot.hOcc 196
  · exact hroot.hOcc 206
  · exact hroot.hOcc 210
  · exact hroot.hOcc 224
  · exact hroot.hOcc 226
  · exact hroot.hOcc 233
  · exact hroot.hOcc 236
  · exact hroot.hOcc 237
  · exact hroot.hOcc 240
  · exact hroot.hOcc 244
  · exact hroot.hOcc 253
  · exact hroot.hOcc 259
  · change (∑ j, (-1 : Int) * x j) ≤ -plane486GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (7 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (38 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (22 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22
  · change (∑ k, (if k = (16 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (3 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (10 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10

end QiushiMatmul
