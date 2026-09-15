import QiushiPlane489GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane489GenLeaf0020Refs : Fin 33 → RowRef 371 32 := ![.occ 96, .occ 104, .occ 108, .occ 109, .occ 128, .occ 130, .occ 139, .occ 140, .occ 149, .occ 172, .occ 175, .occ 184, .occ 195, .occ 208, .occ 213, .occ 228, .occ 274, .occ 282, .occ 292, .occ 307, .occ 321, .occ 337, .occ 342, .occ 345, .occ 350, .occ 354, .occ 362, .sumGe, .branchLe 14 (0), .branchGe 9 (1), .branchLe 5 (0), .branchLe 26 (0), .branchLe 24 (0)]

def plane489GenLeaf0020Mult : Fin 33 → Nat := ![354, 186, 95, 59, 13, 210, 237, 49, 18, 8, 252, 371, 317, 193, 27, 291, 116, 137, 22, 336, 95, 315, 105, 298, 28, 91, 84, 897, 471, 1464, 789, 287, 677]

theorem plane489GenLeaf0020 (x : Fin 32 → Int)
    (hroot : plane489GenOccSys.RootHolds x)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane489GenLeaf0020Refs i).resolveCoeff plane489GenOccSys j)
    (fun i => (plane489GenLeaf0020Refs i).resolveRhs plane489GenOccSys) plane489GenLeaf0020Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane489GenLeaf0020Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 96
  · exact hroot.hOcc 104
  · exact hroot.hOcc 108
  · exact hroot.hOcc 109
  · exact hroot.hOcc 128
  · exact hroot.hOcc 130
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 149
  · exact hroot.hOcc 172
  · exact hroot.hOcc 175
  · exact hroot.hOcc 184
  · exact hroot.hOcc 195
  · exact hroot.hOcc 208
  · exact hroot.hOcc 213
  · exact hroot.hOcc 228
  · exact hroot.hOcc 274
  · exact hroot.hOcc 282
  · exact hroot.hOcc 292
  · exact hroot.hOcc 307
  · exact hroot.hOcc 321
  · exact hroot.hOcc 337
  · exact hroot.hOcc 342
  · exact hroot.hOcc 345
  · exact hroot.hOcc 350
  · exact hroot.hOcc 354
  · exact hroot.hOcc 362
  · change (∑ j, (-1 : Int) * x j) ≤ -plane489GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (9 : Fin 32) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9
  · change (∑ k, (if k = (5 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (26 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (24 : Fin 32) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24

end QiushiMatmul
