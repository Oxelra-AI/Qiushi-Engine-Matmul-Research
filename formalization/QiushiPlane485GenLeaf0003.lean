import QiushiPlane485GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane485GenLeaf0003Refs : Fin 42 → RowRef 421 41 := ![.occ 87, .occ 110, .occ 115, .occ 132, .occ 134, .occ 135, .occ 136, .occ 139, .occ 155, .occ 161, .occ 163, .occ 172, .occ 173, .occ 175, .occ 179, .occ 187, .occ 189, .occ 207, .occ 213, .occ 232, .occ 241, .occ 262, .occ 265, .occ 276, .occ 287, .occ 300, .occ 305, .occ 332, .occ 337, .occ 352, .occ 353, .occ 366, .occ 374, .occ 401, .occ 406, .sumGe, .branchLe 28 (0), .branchLe 21 (0), .branchLe 14 (0), .branchLe 11 (0), .branchLe 39 (0), .branchGe 17 (1)]

def plane485GenLeaf0003Mult : Fin 42 → Nat := ![293165, 108565, 28064, 70776, 120407, 119624, 95134, 31542, 86393, 254767, 25046, 39183, 150988, 20980, 177359, 195824, 84937, 72015, 140307, 142416, 72195, 80641, 115940, 191003, 208047, 180014, 24910, 10917, 21336, 10136, 109132, 13781, 108457, 15648, 14273, 573286, 559013, 220510, 487490, 344255, 439919, 1100604]

theorem plane485GenLeaf0003 (x : Fin 41 → Int)
    (hroot : plane485GenOccSys.RootHolds x)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane485GenLeaf0003Refs i).resolveCoeff plane485GenOccSys j)
    (fun i => (plane485GenLeaf0003Refs i).resolveRhs plane485GenOccSys) plane485GenLeaf0003Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane485GenLeaf0003Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 110
  · exact hroot.hOcc 115
  · exact hroot.hOcc 132
  · exact hroot.hOcc 134
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 139
  · exact hroot.hOcc 155
  · exact hroot.hOcc 161
  · exact hroot.hOcc 163
  · exact hroot.hOcc 172
  · exact hroot.hOcc 173
  · exact hroot.hOcc 175
  · exact hroot.hOcc 179
  · exact hroot.hOcc 187
  · exact hroot.hOcc 189
  · exact hroot.hOcc 207
  · exact hroot.hOcc 213
  · exact hroot.hOcc 232
  · exact hroot.hOcc 241
  · exact hroot.hOcc 262
  · exact hroot.hOcc 265
  · exact hroot.hOcc 276
  · exact hroot.hOcc 287
  · exact hroot.hOcc 300
  · exact hroot.hOcc 305
  · exact hroot.hOcc 332
  · exact hroot.hOcc 337
  · exact hroot.hOcc 352
  · exact hroot.hOcc 353
  · exact hroot.hOcc 366
  · exact hroot.hOcc 374
  · exact hroot.hOcc 401
  · exact hroot.hOcc 406
  · change (∑ j, (-1 : Int) * x j) ≤ -plane485GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (28 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (21 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (14 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (11 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (39 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (17 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17

end QiushiMatmul
