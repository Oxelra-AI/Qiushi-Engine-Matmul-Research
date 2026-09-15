import QiushiPlane485GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane485GenLeaf0038Refs : Fin 42 → RowRef 421 41 := ![.occ 87, .occ 112, .occ 115, .occ 135, .occ 136, .occ 137, .occ 150, .occ 153, .occ 161, .occ 162, .occ 165, .occ 166, .occ 169, .occ 171, .occ 174, .occ 179, .occ 186, .occ 210, .occ 212, .occ 234, .occ 238, .occ 243, .occ 246, .occ 248, .occ 262, .occ 265, .occ 275, .occ 279, .occ 301, .occ 305, .occ 315, .occ 342, .occ 365, .occ 376, .occ 383, .sumGe, .nonneg 0, .nonneg 12, .nonneg 16, .branchGe 28 (1), .branchGe 19 (1), .branchLe 18 (0)]

def plane485GenLeaf0038Mult : Fin 42 → Nat := ![30223, 9961, 2786, 14664, 6216, 9365, 15038, 88, 5129, 6283, 11532, 2879, 10846, 1715, 29965, 2182, 11051, 6112, 28334, 905, 7612, 41689, 4795, 1803, 16743, 1715, 3353, 7257, 2189, 8174, 13180, 20423, 1258, 1715, 2739, 43492, 15424, 1585, 6371, 151366, 174755, 43492]

theorem plane485GenLeaf0038 (x : Fin 41 → Int)
    (hroot : plane485GenOccSys.RootHolds x)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hUB_18 : x 18 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane485GenLeaf0038Refs i).resolveCoeff plane485GenOccSys j)
    (fun i => (plane485GenLeaf0038Refs i).resolveRhs plane485GenOccSys) plane485GenLeaf0038Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane485GenLeaf0038Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 112
  · exact hroot.hOcc 115
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 150
  · exact hroot.hOcc 153
  · exact hroot.hOcc 161
  · exact hroot.hOcc 162
  · exact hroot.hOcc 165
  · exact hroot.hOcc 166
  · exact hroot.hOcc 169
  · exact hroot.hOcc 171
  · exact hroot.hOcc 174
  · exact hroot.hOcc 179
  · exact hroot.hOcc 186
  · exact hroot.hOcc 210
  · exact hroot.hOcc 212
  · exact hroot.hOcc 234
  · exact hroot.hOcc 238
  · exact hroot.hOcc 243
  · exact hroot.hOcc 246
  · exact hroot.hOcc 248
  · exact hroot.hOcc 262
  · exact hroot.hOcc 265
  · exact hroot.hOcc 275
  · exact hroot.hOcc 279
  · exact hroot.hOcc 301
  · exact hroot.hOcc 305
  · exact hroot.hOcc 315
  · exact hroot.hOcc 342
  · exact hroot.hOcc 365
  · exact hroot.hOcc 376
  · exact hroot.hOcc 383
  · change (∑ j, (-1 : Int) * x j) ≤ -plane485GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (12 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (16 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (28 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (19 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (18 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18

end QiushiMatmul
