import QiushiPlane453GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane453GenLeaf0001Refs : Fin 51 → RowRef 210 50 := ![.occ 18, .occ 24, .occ 29, .occ 34, .occ 35, .occ 36, .occ 47, .occ 54, .occ 55, .occ 61, .occ 65, .occ 66, .occ 67, .occ 80, .occ 102, .occ 104, .occ 105, .occ 106, .occ 108, .occ 117, .occ 125, .occ 134, .occ 135, .occ 138, .occ 143, .occ 150, .occ 160, .occ 161, .occ 165, .occ 169, .occ 179, .occ 186, .occ 193, .occ 194, .occ 196, .occ 198, .occ 205, .occ 207, .occ 209, .sumGe, .nonneg 0, .nonneg 22, .nonneg 23, .nonneg 28, .nonneg 31, .nonneg 33, .nonneg 45, .branchLe 35 (0), .branchLe 5 (1), .branchLe 15 (0), .branchGe 9 (1)]

def plane453GenLeaf0001Mult : Fin 51 → Nat := ![6984, 349068, 20956, 294092, 199852, 259436, 159704, 331404, 313656, 113864, 254156, 487476, 287172, 12872, 57488, 105772, 540744, 228308, 186544, 35744, 18140, 78266, 92942, 28394, 80140, 105386, 43326, 75358, 172200, 215430, 70706, 153612, 181820, 9178, 144913, 38163, 297993, 10453, 130844, 957724, 563096, 44096, 580408, 44504, 557964, 67676, 59056, 815700, 433848, 957724, 1619972]

theorem plane453GenLeaf0001 (x : Fin 50 → Int)
    (hroot : plane453GenOccSys.RootHolds x)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hUB_35 : x 35 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (1 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane453GenLeaf0001Refs i).resolveCoeff plane453GenOccSys j)
    (fun i => (plane453GenLeaf0001Refs i).resolveRhs plane453GenOccSys) plane453GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane453GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 18
  · exact hroot.hOcc 24
  · exact hroot.hOcc 29
  · exact hroot.hOcc 34
  · exact hroot.hOcc 35
  · exact hroot.hOcc 36
  · exact hroot.hOcc 47
  · exact hroot.hOcc 54
  · exact hroot.hOcc 55
  · exact hroot.hOcc 61
  · exact hroot.hOcc 65
  · exact hroot.hOcc 66
  · exact hroot.hOcc 67
  · exact hroot.hOcc 80
  · exact hroot.hOcc 102
  · exact hroot.hOcc 104
  · exact hroot.hOcc 105
  · exact hroot.hOcc 106
  · exact hroot.hOcc 108
  · exact hroot.hOcc 117
  · exact hroot.hOcc 125
  · exact hroot.hOcc 134
  · exact hroot.hOcc 135
  · exact hroot.hOcc 138
  · exact hroot.hOcc 143
  · exact hroot.hOcc 150
  · exact hroot.hOcc 160
  · exact hroot.hOcc 161
  · exact hroot.hOcc 165
  · exact hroot.hOcc 169
  · exact hroot.hOcc 179
  · exact hroot.hOcc 186
  · exact hroot.hOcc 193
  · exact hroot.hOcc 194
  · exact hroot.hOcc 196
  · exact hroot.hOcc 198
  · exact hroot.hOcc 205
  · exact hroot.hOcc 207
  · exact hroot.hOcc 209
  · change (∑ j, (-1 : Int) * x j) ≤ -plane453GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (22 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (23 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (28 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (31 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 31
  · change (∑ k, (if k = (33 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (45 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (35 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (5 : Fin 50) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (15 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (9 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9

end QiushiMatmul
