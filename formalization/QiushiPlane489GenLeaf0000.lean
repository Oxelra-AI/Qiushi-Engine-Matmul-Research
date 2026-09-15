import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0000Refs : Fin 33 → RowRef 371 32 := ![.occ 96, .occ 97, .occ 102, .occ 105, .occ 129, .occ 131, .occ 140, .occ 147, .occ 154, .occ 161, .occ 163, .occ 164, .occ 165, .occ 178, .occ 186, .occ 187, .occ 206, .occ 208, .occ 216, .occ 240, .occ 243, .occ 286, .occ 304, .occ 338, .occ 345, .occ 350, .occ 363, .sumGe, .branchLe 14 (0), .branchLe 9 (0), .branchLe 31 (0), .branchLe 25 (0), .branchLe 10 (0)]

def plane489GenLeaf0000Mult : Fin 33 → Nat := ![432, 381, 526, 120, 26, 103, 106, 258, 94, 155, 59, 182, 37, 4, 53, 254, 183, 70, 202, 142, 40, 13, 18, 44, 84, 392, 27, 703, 648, 703, 548, 445, 703]

theorem plane489GenLeaf0000 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0000Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0000Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 96
  · exact hroot.hOcc 97
  · exact hroot.hOcc 102
  · exact hroot.hOcc 105
  · exact hroot.hOcc 129
  · exact hroot.hOcc 131
  · exact hroot.hOcc 140
  · exact hroot.hOcc 147
  · exact hroot.hOcc 154
  · exact hroot.hOcc 161
  · exact hroot.hOcc 163
  · exact hroot.hOcc 164
  · exact hroot.hOcc 165
  · exact hroot.hOcc 178
  · exact hroot.hOcc 186
  · exact hroot.hOcc 187
  · exact hroot.hOcc 206
  · exact hroot.hOcc 208
  · exact hroot.hOcc 216
  · exact hroot.hOcc 240
  · exact hroot.hOcc 243
  · exact hroot.hOcc 286
  · exact hroot.hOcc 304
  · exact hroot.hOcc 338
  · exact hroot.hOcc 345
  · exact hroot.hOcc 350
  · exact hroot.hOcc 363
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (9 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (31 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (25 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (10 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10

end QiushiMatmul
