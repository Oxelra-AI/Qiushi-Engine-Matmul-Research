import QiushiPlane454GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane454GenLeaf0002Refs : Fin 56 → RowRef 174 55 := ![.occ 11, .occ 13, .occ 14, .occ 19, .occ 23, .occ 24, .occ 30, .occ 36, .occ 38, .occ 41, .occ 47, .occ 50, .occ 51, .occ 53, .occ 54, .occ 56, .occ 61, .occ 64, .occ 81, .occ 82, .occ 87, .occ 88, .occ 89, .occ 90, .occ 94, .occ 95, .occ 111, .occ 122, .occ 124, .occ 128, .occ 131, .occ 139, .occ 140, .occ 143, .occ 144, .occ 150, .occ 152, .occ 158, .occ 159, .occ 160, .occ 162, .occ 165, .occ 166, .occ 170, .occ 171, .sumGe, .nonneg 13, .nonneg 17, .nonneg 24, .nonneg 27, .nonneg 46, .nonneg 52, .nonneg 54, .branchLe 2 (0), .branchLe 4 (0), .branchGe 12 (1)]

def plane454GenLeaf0002Mult : Fin 56 → Nat := ![167306, 348440, 82242, 148330, 58172, 321898, 202890, 401758, 46672, 177412, 223010, 187932, 80016, 74876, 574330, 159818, 494382, 165106, 161164, 6800, 52744, 167088, 42992, 346438, 1592, 42518, 147566, 93864, 134304, 37212, 105974, 101704, 16570, 160922, 75440, 243452, 281954, 58528, 122690, 169316, 88104, 61993, 76249, 22515, 35107, 919108, 247894, 324700, 299446, 175820, 114274, 254514, 557812, 192620, 772476, 2825772]

theorem plane454GenLeaf0002 (x : Fin 55 → Int)
    (hroot : plane454GenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane454GenLeaf0002Refs i).resolveCoeff plane454GenOccSys j)
    (fun i => (plane454GenLeaf0002Refs i).resolveRhs plane454GenOccSys) plane454GenLeaf0002Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane454GenLeaf0002Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 11
  · exact hroot.hOcc 13
  · exact hroot.hOcc 14
  · exact hroot.hOcc 19
  · exact hroot.hOcc 23
  · exact hroot.hOcc 24
  · exact hroot.hOcc 30
  · exact hroot.hOcc 36
  · exact hroot.hOcc 38
  · exact hroot.hOcc 41
  · exact hroot.hOcc 47
  · exact hroot.hOcc 50
  · exact hroot.hOcc 51
  · exact hroot.hOcc 53
  · exact hroot.hOcc 54
  · exact hroot.hOcc 56
  · exact hroot.hOcc 61
  · exact hroot.hOcc 64
  · exact hroot.hOcc 81
  · exact hroot.hOcc 82
  · exact hroot.hOcc 87
  · exact hroot.hOcc 88
  · exact hroot.hOcc 89
  · exact hroot.hOcc 90
  · exact hroot.hOcc 94
  · exact hroot.hOcc 95
  · exact hroot.hOcc 111
  · exact hroot.hOcc 122
  · exact hroot.hOcc 124
  · exact hroot.hOcc 128
  · exact hroot.hOcc 131
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 143
  · exact hroot.hOcc 144
  · exact hroot.hOcc 150
  · exact hroot.hOcc 152
  · exact hroot.hOcc 158
  · exact hroot.hOcc 159
  · exact hroot.hOcc 160
  · exact hroot.hOcc 162
  · exact hroot.hOcc 165
  · exact hroot.hOcc 166
  · exact hroot.hOcc 170
  · exact hroot.hOcc 171
  · change (∑ j, (-1 : Int) * x j) ≤ -plane454GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (13 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (17 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (24 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (27 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27
  · change (∑ k, (if k = (46 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (52 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (54 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 54
  · change (∑ k, (if k = (2 : Fin 55) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (4 : Fin 55) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (12 : Fin 55) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12

end QiushiMatmul
