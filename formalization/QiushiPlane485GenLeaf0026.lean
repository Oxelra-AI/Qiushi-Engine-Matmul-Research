import QiushiPlane485GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane485GenLeaf0026Refs : Fin 39 → RowRef 421 41 := ![.occ 87, .occ 88, .occ 136, .occ 140, .occ 146, .occ 148, .occ 150, .occ 155, .occ 173, .occ 180, .occ 181, .occ 195, .occ 202, .occ 210, .occ 224, .occ 243, .occ 245, .occ 253, .occ 263, .occ 267, .occ 274, .occ 285, .occ 287, .occ 289, .occ 290, .occ 298, .occ 307, .occ 312, .occ 336, .occ 352, .occ 390, .occ 402, .occ 416, .sumGe, .nonneg 4, .nonneg 12, .branchLe 28 (0), .branchGe 21 (1), .branchGe 32 (1)]

def plane485GenLeaf0026Mult : Fin 39 → Nat := ![1578, 454, 1542, 369, 1895, 462, 340, 340, 1495, 754, 4265, 1518, 1805, 1061, 4158, 1220, 551, 984, 727, 518, 720, 601, 104, 523, 933, 993, 1032, 444, 2122, 387, 24, 533, 107, 4709, 544, 369, 1421, 19329, 18731]

theorem plane485GenLeaf0026 (x : Fin 41 → Int)
    (hroot : plane485GenOccSys.RootHolds x)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hUB_28 : x 28 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane485GenLeaf0026Refs i).resolveCoeff plane485GenOccSys j)
    (fun i => (plane485GenLeaf0026Refs i).resolveRhs plane485GenOccSys) plane485GenLeaf0026Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane485GenLeaf0026Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 88
  · exact hroot.hOcc 136
  · exact hroot.hOcc 140
  · exact hroot.hOcc 146
  · exact hroot.hOcc 148
  · exact hroot.hOcc 150
  · exact hroot.hOcc 155
  · exact hroot.hOcc 173
  · exact hroot.hOcc 180
  · exact hroot.hOcc 181
  · exact hroot.hOcc 195
  · exact hroot.hOcc 202
  · exact hroot.hOcc 210
  · exact hroot.hOcc 224
  · exact hroot.hOcc 243
  · exact hroot.hOcc 245
  · exact hroot.hOcc 253
  · exact hroot.hOcc 263
  · exact hroot.hOcc 267
  · exact hroot.hOcc 274
  · exact hroot.hOcc 285
  · exact hroot.hOcc 287
  · exact hroot.hOcc 289
  · exact hroot.hOcc 290
  · exact hroot.hOcc 298
  · exact hroot.hOcc 307
  · exact hroot.hOcc 312
  · exact hroot.hOcc 336
  · exact hroot.hOcc 352
  · exact hroot.hOcc 390
  · exact hroot.hOcc 402
  · exact hroot.hOcc 416
  · change (∑ j, (-1 : Int) * x j) ≤ -plane485GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (4 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (12 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (28 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (21 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21
  · change (∑ k, (if k = (32 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32

end QiushiMatmul
