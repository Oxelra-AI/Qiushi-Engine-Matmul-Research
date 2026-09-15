import QiushiPlane454GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane454GenLeaf0001Refs : Fin 56 → RowRef 174 55 := ![.occ 10, .occ 24, .occ 26, .occ 27, .occ 28, .occ 32, .occ 36, .occ 40, .occ 41, .occ 43, .occ 48, .occ 49, .occ 51, .occ 52, .occ 56, .occ 64, .occ 66, .occ 68, .occ 72, .occ 81, .occ 84, .occ 89, .occ 90, .occ 91, .occ 93, .occ 97, .occ 100, .occ 104, .occ 108, .occ 111, .occ 112, .occ 113, .occ 115, .occ 122, .occ 128, .occ 130, .occ 137, .occ 138, .occ 139, .occ 140, .occ 141, .occ 143, .occ 145, .occ 159, .occ 169, .occ 170, .sumGe, .nonneg 24, .nonneg 27, .nonneg 30, .nonneg 33, .nonneg 38, .branchLe 2 (0), .branchLe 4 (0), .branchLe 12 (0), .branchGe 26 (1)]

def plane454GenLeaf0001Mult : Fin 56 → Nat := ![61910, 459259, 1015930, 250441, 91816, 554292, 719191, 118970, 312034, 643931, 24734, 49885, 316301, 64734, 19322, 540779, 461425, 455344, 103910, 555207, 107703, 160040, 401143, 316141, 49179, 71671, 218100, 53635, 80624, 213306, 196283, 57712, 72434, 193900, 179847, 216926, 197471, 2299, 48951, 156482, 50044, 294871, 88463, 135266, 43146, 205054, 1219116, 417148, 359363, 39779, 97532, 150963, 569872, 902975, 1083850, 4152423]

theorem plane454GenLeaf0001 (x : Fin 55 → Int)
    (hroot : plane454GenOccSys.RootHolds x)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane454GenLeaf0001Refs i).resolveCoeff plane454GenOccSys j)
    (fun i => (plane454GenLeaf0001Refs i).resolveRhs plane454GenOccSys) plane454GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane454GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 10
  · exact hroot.hOcc 24
  · exact hroot.hOcc 26
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · exact hroot.hOcc 32
  · exact hroot.hOcc 36
  · exact hroot.hOcc 40
  · exact hroot.hOcc 41
  · exact hroot.hOcc 43
  · exact hroot.hOcc 48
  · exact hroot.hOcc 49
  · exact hroot.hOcc 51
  · exact hroot.hOcc 52
  · exact hroot.hOcc 56
  · exact hroot.hOcc 64
  · exact hroot.hOcc 66
  · exact hroot.hOcc 68
  · exact hroot.hOcc 72
  · exact hroot.hOcc 81
  · exact hroot.hOcc 84
  · exact hroot.hOcc 89
  · exact hroot.hOcc 90
  · exact hroot.hOcc 91
  · exact hroot.hOcc 93
  · exact hroot.hOcc 97
  · exact hroot.hOcc 100
  · exact hroot.hOcc 104
  · exact hroot.hOcc 108
  · exact hroot.hOcc 111
  · exact hroot.hOcc 112
  · exact hroot.hOcc 113
  · exact hroot.hOcc 115
  · exact hroot.hOcc 122
  · exact hroot.hOcc 128
  · exact hroot.hOcc 130
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 141
  · exact hroot.hOcc 143
  · exact hroot.hOcc 145
  · exact hroot.hOcc 159
  · exact hroot.hOcc 169
  · exact hroot.hOcc 170
  · change (∑ j, (-1 : Int) * x j) ≤ -plane454GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (24 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (27 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27
  · change (∑ k, (if k = (30 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (33 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (38 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (2 : Fin 55) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (4 : Fin 55) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (12 : Fin 55) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (26 : Fin 55) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26

end QiushiMatmul
