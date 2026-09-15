import QiushiPlane485GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane485GenLeaf0014Refs : Fin 42 → RowRef 421 41 := ![.occ 87, .occ 105, .occ 118, .occ 120, .occ 134, .occ 136, .occ 143, .occ 149, .occ 154, .occ 167, .occ 168, .occ 179, .occ 184, .occ 190, .occ 203, .occ 211, .occ 215, .occ 218, .occ 228, .occ 234, .occ 252, .occ 262, .occ 265, .occ 282, .occ 298, .occ 326, .occ 336, .occ 366, .occ 372, .occ 375, .occ 380, .occ 392, .occ 395, .sumGe, .branchLe 28 (0), .branchLe 21 (0), .branchGe 14 (1), .branchLe 29 (0), .branchLe 13 (0), .branchLe 15 (0), .branchLe 31 (0), .branchLe 4 (0)]

def plane485GenLeaf0014Mult : Fin 42 → Nat := ![20986, 1232, 11993, 29402, 6412, 28815, 17431, 15720, 49170, 22654, 21777, 18757, 15833, 15089, 5617, 6215, 6606, 1819, 1426, 4159, 36084, 131, 27592, 6976, 5257, 12083, 10243, 2518, 15707, 18550, 1702, 16005, 10125, 82321, 80502, 66821, 138887, 48682, 51399, 55396, 46106, 82321]

theorem plane485GenLeaf0014 (x : Fin 41 → Int)
    (hroot : plane485GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane485GenLeaf0014Refs i).resolveCoeff plane485GenOccSys j)
    (fun i => (plane485GenLeaf0014Refs i).resolveRhs plane485GenOccSys) plane485GenLeaf0014Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane485GenLeaf0014Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 105
  · exact hroot.hOcc 118
  · exact hroot.hOcc 120
  · exact hroot.hOcc 134
  · exact hroot.hOcc 136
  · exact hroot.hOcc 143
  · exact hroot.hOcc 149
  · exact hroot.hOcc 154
  · exact hroot.hOcc 167
  · exact hroot.hOcc 168
  · exact hroot.hOcc 179
  · exact hroot.hOcc 184
  · exact hroot.hOcc 190
  · exact hroot.hOcc 203
  · exact hroot.hOcc 211
  · exact hroot.hOcc 215
  · exact hroot.hOcc 218
  · exact hroot.hOcc 228
  · exact hroot.hOcc 234
  · exact hroot.hOcc 252
  · exact hroot.hOcc 262
  · exact hroot.hOcc 265
  · exact hroot.hOcc 282
  · exact hroot.hOcc 298
  · exact hroot.hOcc 326
  · exact hroot.hOcc 336
  · exact hroot.hOcc 366
  · exact hroot.hOcc 372
  · exact hroot.hOcc 375
  · exact hroot.hOcc 380
  · exact hroot.hOcc 392
  · exact hroot.hOcc 395
  · change (∑ j, (-1 : Int) * x j) ≤ -plane485GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (28 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (21 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (14 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (29 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (13 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (15 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (31 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (4 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4

end QiushiMatmul
