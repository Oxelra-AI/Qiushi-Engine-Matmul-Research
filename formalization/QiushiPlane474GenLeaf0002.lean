import QiushiPlane474GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane474GenLeaf0002Refs : Fin 61 → RowRef 146 60 := ![.occ 3, .occ 4, .occ 5, .occ 7, .occ 11, .occ 21, .occ 22, .occ 24, .occ 26, .occ 27, .occ 28, .occ 29, .occ 30, .occ 32, .occ 33, .occ 34, .occ 36, .occ 38, .occ 40, .occ 43, .occ 46, .occ 48, .occ 49, .occ 50, .occ 51, .occ 52, .occ 53, .occ 63, .occ 64, .occ 71, .occ 77, .occ 80, .occ 82, .occ 86, .occ 87, .occ 88, .occ 93, .occ 97, .occ 98, .occ 101, .occ 103, .occ 104, .occ 110, .occ 112, .occ 119, .occ 121, .occ 125, .occ 127, .occ 130, .occ 131, .occ 136, .occ 138, .occ 143, .occ 144, .sumGe, .nonneg 26, .nonneg 35, .nonneg 52, .branchLe 44 (0), .branchLe 43 (0), .branchGe 22 (1)]

def plane474GenLeaf0002Mult : Fin 61 → Nat := ![591732, 571961, 266502, 268440, 30473, 490572, 320308, 288421, 668365, 537150, 373040, 255702, 25444, 542356, 138340, 1000139, 213679, 928138, 1286988, 235030, 435270, 184830, 166894, 807078, 261102, 88978, 758272, 499412, 1152180, 303204, 866944, 425838, 242382, 262800, 24622, 313866, 20898, 5292, 170584, 1162, 105184, 241080, 12668, 189660, 136746, 311528, 73182, 33386, 214088, 44480, 268468, 464044, 138386, 24924, 1846486, 84494, 102214, 1853138, 1684816, 520318, 5954960]

theorem plane474GenLeaf0002 (x : Fin 60 → Int)
    (hroot : plane474GenOccSys.RootHolds x)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_43 : x 43 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane474GenLeaf0002Refs i).resolveCoeff plane474GenOccSys j)
    (fun i => (plane474GenLeaf0002Refs i).resolveRhs plane474GenOccSys) plane474GenLeaf0002Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane474GenLeaf0002Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 3
  · exact hroot.hOcc 4
  · exact hroot.hOcc 5
  · exact hroot.hOcc 7
  · exact hroot.hOcc 11
  · exact hroot.hOcc 21
  · exact hroot.hOcc 22
  · exact hroot.hOcc 24
  · exact hroot.hOcc 26
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · exact hroot.hOcc 29
  · exact hroot.hOcc 30
  · exact hroot.hOcc 32
  · exact hroot.hOcc 33
  · exact hroot.hOcc 34
  · exact hroot.hOcc 36
  · exact hroot.hOcc 38
  · exact hroot.hOcc 40
  · exact hroot.hOcc 43
  · exact hroot.hOcc 46
  · exact hroot.hOcc 48
  · exact hroot.hOcc 49
  · exact hroot.hOcc 50
  · exact hroot.hOcc 51
  · exact hroot.hOcc 52
  · exact hroot.hOcc 53
  · exact hroot.hOcc 63
  · exact hroot.hOcc 64
  · exact hroot.hOcc 71
  · exact hroot.hOcc 77
  · exact hroot.hOcc 80
  · exact hroot.hOcc 82
  · exact hroot.hOcc 86
  · exact hroot.hOcc 87
  · exact hroot.hOcc 88
  · exact hroot.hOcc 93
  · exact hroot.hOcc 97
  · exact hroot.hOcc 98
  · exact hroot.hOcc 101
  · exact hroot.hOcc 103
  · exact hroot.hOcc 104
  · exact hroot.hOcc 110
  · exact hroot.hOcc 112
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 125
  · exact hroot.hOcc 127
  · exact hroot.hOcc 130
  · exact hroot.hOcc 131
  · exact hroot.hOcc 136
  · exact hroot.hOcc 138
  · exact hroot.hOcc 143
  · exact hroot.hOcc 144
  · change (∑ j, (-1 : Int) * x j) ≤ -plane474GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (26 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (35 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 35
  · change (∑ k, (if k = (52 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (44 : Fin 60) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (43 : Fin 60) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (22 : Fin 60) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22

end QiushiMatmul
