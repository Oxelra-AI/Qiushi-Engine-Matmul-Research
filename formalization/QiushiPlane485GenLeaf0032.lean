import QiushiPlane485GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane485GenLeaf0032Refs : Fin 42 → RowRef 421 41 := ![.occ 87, .occ 101, .occ 135, .occ 136, .occ 146, .occ 152, .occ 158, .occ 160, .occ 178, .occ 199, .occ 210, .occ 213, .occ 218, .occ 224, .occ 232, .occ 238, .occ 243, .occ 245, .occ 246, .occ 252, .occ 257, .occ 258, .occ 269, .occ 287, .occ 299, .occ 301, .occ 316, .occ 324, .occ 336, .occ 358, .occ 368, .occ 399, .occ 405, .occ 408, .occ 416, .sumGe, .branchGe 28 (1), .branchLe 19 (0), .branchLe 22 (0), .branchLe 0 (0), .branchLe 35 (0), .branchGe 6 (1)]

def plane485GenLeaf0032Mult : Fin 42 → Nat := ![82054, 69213, 55599, 94273, 2637, 25765, 17502, 18524, 26671, 49366, 4947, 6597, 22191, 730, 40866, 39479, 32150, 71817, 533, 30603, 4668, 5530, 19349, 24733, 47864, 44814, 1731, 9586, 825, 11177, 38189, 2000, 41856, 906, 23004, 159133, 355296, 110326, 159133, 22234, 90983, 319500]

theorem plane485GenLeaf0032 (x : Fin 41 → Int)
    (hroot : plane485GenOccSys.RootHolds x)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane485GenLeaf0032Refs i).resolveCoeff plane485GenOccSys j)
    (fun i => (plane485GenLeaf0032Refs i).resolveRhs plane485GenOccSys) plane485GenLeaf0032Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane485GenLeaf0032Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 101
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 146
  · exact hroot.hOcc 152
  · exact hroot.hOcc 158
  · exact hroot.hOcc 160
  · exact hroot.hOcc 178
  · exact hroot.hOcc 199
  · exact hroot.hOcc 210
  · exact hroot.hOcc 213
  · exact hroot.hOcc 218
  · exact hroot.hOcc 224
  · exact hroot.hOcc 232
  · exact hroot.hOcc 238
  · exact hroot.hOcc 243
  · exact hroot.hOcc 245
  · exact hroot.hOcc 246
  · exact hroot.hOcc 252
  · exact hroot.hOcc 257
  · exact hroot.hOcc 258
  · exact hroot.hOcc 269
  · exact hroot.hOcc 287
  · exact hroot.hOcc 299
  · exact hroot.hOcc 301
  · exact hroot.hOcc 316
  · exact hroot.hOcc 324
  · exact hroot.hOcc 336
  · exact hroot.hOcc 358
  · exact hroot.hOcc 368
  · exact hroot.hOcc 399
  · exact hroot.hOcc 405
  · exact hroot.hOcc 408
  · exact hroot.hOcc 416
  · change (∑ j, (-1 : Int) * x j) ≤ -plane485GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (28 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (19 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (22 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (0 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (35 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (6 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6

end QiushiMatmul
