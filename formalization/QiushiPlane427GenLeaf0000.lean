import QiushiPlane427GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane427GenLeaf0000Refs : Fin 51 → RowRef 237 50 := ![.occ 7, .occ 8, .occ 9, .occ 20, .occ 27, .occ 40, .occ 41, .occ 46, .occ 47, .occ 59, .occ 65, .occ 66, .occ 89, .occ 102, .occ 111, .occ 125, .occ 133, .occ 137, .occ 159, .occ 160, .occ 162, .occ 163, .occ 165, .occ 173, .occ 175, .occ 176, .occ 177, .occ 180, .occ 187, .occ 192, .occ 194, .occ 195, .occ 200, .occ 203, .occ 204, .occ 205, .occ 207, .occ 208, .occ 215, .sumGe, .nonneg 20, .nonneg 25, .nonneg 38, .nonneg 44, .nonneg 49, .branchLe 26 (0), .branchLe 15 (0), .branchLe 35 (0), .branchLe 45 (0), .branchLe 18 (0), .branchLe 28 (0)]

def plane427GenLeaf0000Mult : Fin 51 → Nat := ![89612, 91991, 52469, 60537, 12549, 593, 55154, 16948, 19212, 28571, 10792, 33517, 14047, 40160, 2881, 32594, 35200, 31656, 9639, 7359, 10778, 31251, 3717, 8166, 49004, 18551, 26121, 500, 22657, 29031, 2584, 65661, 5726, 56867, 14023, 16116, 22129, 17357, 21817, 157315, 14320, 19610, 8914, 19050, 31154, 18116, 55746, 127188, 153598, 143292, 128960]

theorem plane427GenLeaf0000 (x : Fin 50 → Int)
    (hroot : plane427GenOccSys.RootHolds x)
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    (hUB_45 : x 45 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane427GenLeaf0000Refs i).resolveCoeff plane427GenOccSys j)
    (fun i => (plane427GenLeaf0000Refs i).resolveRhs plane427GenOccSys) plane427GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane427GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 7
  · exact hroot.hOcc 8
  · exact hroot.hOcc 9
  · exact hroot.hOcc 20
  · exact hroot.hOcc 27
  · exact hroot.hOcc 40
  · exact hroot.hOcc 41
  · exact hroot.hOcc 46
  · exact hroot.hOcc 47
  · exact hroot.hOcc 59
  · exact hroot.hOcc 65
  · exact hroot.hOcc 66
  · exact hroot.hOcc 89
  · exact hroot.hOcc 102
  · exact hroot.hOcc 111
  · exact hroot.hOcc 125
  · exact hroot.hOcc 133
  · exact hroot.hOcc 137
  · exact hroot.hOcc 159
  · exact hroot.hOcc 160
  · exact hroot.hOcc 162
  · exact hroot.hOcc 163
  · exact hroot.hOcc 165
  · exact hroot.hOcc 173
  · exact hroot.hOcc 175
  · exact hroot.hOcc 176
  · exact hroot.hOcc 177
  · exact hroot.hOcc 180
  · exact hroot.hOcc 187
  · exact hroot.hOcc 192
  · exact hroot.hOcc 194
  · exact hroot.hOcc 195
  · exact hroot.hOcc 200
  · exact hroot.hOcc 203
  · exact hroot.hOcc 204
  · exact hroot.hOcc 205
  · exact hroot.hOcc 207
  · exact hroot.hOcc 208
  · exact hroot.hOcc 215
  · change (∑ j, (-1 : Int) * x j) ≤ -plane427GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (20 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (25 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (38 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (44 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (49 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (26 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (15 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (35 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (45 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_45
  · change (∑ k, (if k = (18 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (28 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28

end QiushiMatmul
