import QiushiPlane485GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane485GenLeaf0021Refs : Fin 42 → RowRef 421 41 := ![.occ 87, .occ 98, .occ 133, .occ 135, .occ 136, .occ 147, .occ 156, .occ 162, .occ 164, .occ 166, .occ 168, .occ 175, .occ 177, .occ 179, .occ 187, .occ 191, .occ 195, .occ 207, .occ 210, .occ 213, .occ 224, .occ 228, .occ 257, .occ 262, .occ 297, .occ 325, .occ 335, .occ 343, .occ 344, .occ 352, .occ 353, .occ 374, .occ 381, .occ 393, .occ 418, .sumGe, .branchLe 28 (0), .branchGe 21 (1), .branchLe 32 (0), .branchLe 25 (0), .branchLe 23 (0), .branchLe 1 (0)]

def plane485GenLeaf0021Mult : Fin 42 → Nat := ![759822, 498854, 15558, 222337, 558157, 400365, 108460, 134746, 39599, 335946, 7949, 247953, 377412, 107804, 43206, 44971, 506199, 453883, 486755, 193970, 630446, 298247, 32203, 87107, 250259, 30548, 382561, 291602, 93841, 88911, 362068, 71512, 4909, 43001, 16265, 1365356, 1365356, 3473691, 663398, 215233, 804730, 1143019]

theorem plane485GenLeaf0021 (x : Fin 41 → Int)
    (hroot : plane485GenOccSys.RootHolds x)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane485GenLeaf0021Refs i).resolveCoeff plane485GenOccSys j)
    (fun i => (plane485GenLeaf0021Refs i).resolveRhs plane485GenOccSys) plane485GenLeaf0021Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane485GenLeaf0021Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 98
  · exact hroot.hOcc 133
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 147
  · exact hroot.hOcc 156
  · exact hroot.hOcc 162
  · exact hroot.hOcc 164
  · exact hroot.hOcc 166
  · exact hroot.hOcc 168
  · exact hroot.hOcc 175
  · exact hroot.hOcc 177
  · exact hroot.hOcc 179
  · exact hroot.hOcc 187
  · exact hroot.hOcc 191
  · exact hroot.hOcc 195
  · exact hroot.hOcc 207
  · exact hroot.hOcc 210
  · exact hroot.hOcc 213
  · exact hroot.hOcc 224
  · exact hroot.hOcc 228
  · exact hroot.hOcc 257
  · exact hroot.hOcc 262
  · exact hroot.hOcc 297
  · exact hroot.hOcc 325
  · exact hroot.hOcc 335
  · exact hroot.hOcc 343
  · exact hroot.hOcc 344
  · exact hroot.hOcc 352
  · exact hroot.hOcc 353
  · exact hroot.hOcc 374
  · exact hroot.hOcc 381
  · exact hroot.hOcc 393
  · exact hroot.hOcc 418
  · change (∑ j, (-1 : Int) * x j) ≤ -plane485GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (28 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (21 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21
  · change (∑ k, (if k = (32 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (25 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (23 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (1 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1

end QiushiMatmul
