import QiushiPlane457GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane457GenLeaf0000Refs : Fin 50 → RowRef 178 49 := ![.occ 30, .occ 33, .occ 38, .occ 40, .occ 42, .occ 51, .occ 53, .occ 54, .occ 56, .occ 57, .occ 62, .occ 63, .occ 69, .occ 77, .occ 78, .occ 80, .occ 85, .occ 88, .occ 91, .occ 92, .occ 94, .occ 95, .occ 97, .occ 102, .occ 104, .occ 106, .occ 110, .occ 111, .occ 113, .occ 114, .occ 129, .occ 131, .occ 133, .occ 135, .occ 142, .occ 143, .occ 144, .occ 147, .occ 148, .occ 149, .occ 158, .occ 164, .occ 165, .occ 170, .occ 175, .sumGe, .nonneg 18, .branchLe 3 (0), .branchLe 1 (0), .branchLe 4 (0)]

def plane457GenLeaf0000Mult : Fin 50 → Nat := ![1145428, 365554, 3176800, 7075086, 3164358, 1726120, 2615216, 2866830, 5272690, 2626880, 346772, 1485506, 4921582, 9319114, 6441620, 3582432, 355862, 7789272, 2134280, 12320530, 4938256, 10970252, 4209640, 18272, 3396636, 4130804, 1826045, 2380577, 1094706, 1803052, 3461698, 2396926, 2891344, 3404570, 4252510, 302951, 3110591, 4101337, 1897658, 1148299, 1895340, 6980189, 1933887, 889644, 623980, 23735588, 9659046, 18814006, 23735588, 23735588]

theorem plane457GenLeaf0000 (x : Fin 49 → Int)
    (hroot : plane457GenOccSys.RootHolds x)
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane457GenLeaf0000Refs i).resolveCoeff plane457GenOccSys j)
    (fun i => (plane457GenLeaf0000Refs i).resolveRhs plane457GenOccSys) plane457GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane457GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 30
  · exact hroot.hOcc 33
  · exact hroot.hOcc 38
  · exact hroot.hOcc 40
  · exact hroot.hOcc 42
  · exact hroot.hOcc 51
  · exact hroot.hOcc 53
  · exact hroot.hOcc 54
  · exact hroot.hOcc 56
  · exact hroot.hOcc 57
  · exact hroot.hOcc 62
  · exact hroot.hOcc 63
  · exact hroot.hOcc 69
  · exact hroot.hOcc 77
  · exact hroot.hOcc 78
  · exact hroot.hOcc 80
  · exact hroot.hOcc 85
  · exact hroot.hOcc 88
  · exact hroot.hOcc 91
  · exact hroot.hOcc 92
  · exact hroot.hOcc 94
  · exact hroot.hOcc 95
  · exact hroot.hOcc 97
  · exact hroot.hOcc 102
  · exact hroot.hOcc 104
  · exact hroot.hOcc 106
  · exact hroot.hOcc 110
  · exact hroot.hOcc 111
  · exact hroot.hOcc 113
  · exact hroot.hOcc 114
  · exact hroot.hOcc 129
  · exact hroot.hOcc 131
  · exact hroot.hOcc 133
  · exact hroot.hOcc 135
  · exact hroot.hOcc 142
  · exact hroot.hOcc 143
  · exact hroot.hOcc 144
  · exact hroot.hOcc 147
  · exact hroot.hOcc 148
  · exact hroot.hOcc 149
  · exact hroot.hOcc 158
  · exact hroot.hOcc 164
  · exact hroot.hOcc 165
  · exact hroot.hOcc 170
  · exact hroot.hOcc 175
  · change (∑ j, (-1 : Int) * x j) ≤ -plane457GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (18 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (3 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (1 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (4 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4

end QiushiMatmul
