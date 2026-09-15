import QiushiPlane466GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane466GenLeaf0002Refs : Fin 51 → RowRef 210 50 := ![.occ 23, .occ 25, .occ 27, .occ 30, .occ 35, .occ 39, .occ 46, .occ 55, .occ 63, .occ 64, .occ 65, .occ 76, .occ 84, .occ 85, .occ 88, .occ 94, .occ 100, .occ 102, .occ 107, .occ 110, .occ 111, .occ 112, .occ 113, .occ 119, .occ 124, .occ 133, .occ 140, .occ 141, .occ 147, .occ 148, .occ 149, .occ 153, .occ 157, .occ 159, .occ 160, .occ 162, .occ 172, .occ 174, .occ 189, .occ 190, .occ 195, .occ 204, .occ 205, .sumGe, .nonneg 0, .nonneg 32, .nonneg 44, .branchLe 24 (0), .branchLe 19 (0), .branchLe 26 (0), .branchGe 28 (1)]

def plane466GenLeaf0002Mult : Fin 51 → Nat := ![1282, 10025, 14336, 8379, 6732, 8784, 15091, 4435, 8129, 2361, 2121, 5651, 5061, 2839, 5974, 9012, 4348, 10254, 954, 4672, 17521, 1793, 7901, 634, 8150, 5280, 4178, 5455, 10618, 3420, 9478, 290, 2507, 6832, 2921, 990, 2509, 7674, 99, 883, 4323, 626, 2193, 30350, 52838, 3736, 2988, 30350, 30350, 26304, 102348]

theorem plane466GenLeaf0002 (x : Fin 50 → Int)
    (hroot : plane466GenOccSys.RootHolds x)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane466GenLeaf0002Refs i).resolveCoeff plane466GenOccSys j)
    (fun i => (plane466GenLeaf0002Refs i).resolveRhs plane466GenOccSys) plane466GenLeaf0002Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane466GenLeaf0002Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 23
  · exact hroot.hOcc 25
  · exact hroot.hOcc 27
  · exact hroot.hOcc 30
  · exact hroot.hOcc 35
  · exact hroot.hOcc 39
  · exact hroot.hOcc 46
  · exact hroot.hOcc 55
  · exact hroot.hOcc 63
  · exact hroot.hOcc 64
  · exact hroot.hOcc 65
  · exact hroot.hOcc 76
  · exact hroot.hOcc 84
  · exact hroot.hOcc 85
  · exact hroot.hOcc 88
  · exact hroot.hOcc 94
  · exact hroot.hOcc 100
  · exact hroot.hOcc 102
  · exact hroot.hOcc 107
  · exact hroot.hOcc 110
  · exact hroot.hOcc 111
  · exact hroot.hOcc 112
  · exact hroot.hOcc 113
  · exact hroot.hOcc 119
  · exact hroot.hOcc 124
  · exact hroot.hOcc 133
  · exact hroot.hOcc 140
  · exact hroot.hOcc 141
  · exact hroot.hOcc 147
  · exact hroot.hOcc 148
  · exact hroot.hOcc 149
  · exact hroot.hOcc 153
  · exact hroot.hOcc 157
  · exact hroot.hOcc 159
  · exact hroot.hOcc 160
  · exact hroot.hOcc 162
  · exact hroot.hOcc 172
  · exact hroot.hOcc 174
  · exact hroot.hOcc 189
  · exact hroot.hOcc 190
  · exact hroot.hOcc 195
  · exact hroot.hOcc 204
  · exact hroot.hOcc 205
  · change (∑ j, (-1 : Int) * x j) ≤ -plane466GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (32 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (44 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (24 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (19 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (26 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (28 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28

end QiushiMatmul
