import QiushiPlane453GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane453GenLeaf0002Refs : Fin 51 → RowRef 210 50 := ![.occ 30, .occ 35, .occ 38, .occ 46, .occ 48, .occ 52, .occ 56, .occ 58, .occ 62, .occ 68, .occ 81, .occ 85, .occ 94, .occ 103, .occ 104, .occ 105, .occ 108, .occ 116, .occ 133, .occ 136, .occ 137, .occ 138, .occ 139, .occ 150, .occ 156, .occ 159, .occ 161, .occ 163, .occ 168, .occ 172, .occ 179, .occ 181, .occ 185, .occ 187, .occ 193, .occ 199, .occ 209, .sumGe, .nonneg 0, .nonneg 22, .nonneg 23, .nonneg 25, .nonneg 28, .nonneg 39, .nonneg 48, .branchLe 35 (0), .branchLe 5 (1), .branchGe 15 (1), .branchLe 1 (0), .branchLe 17 (0), .branchLe 11 (0)]

def plane453GenLeaf0002Mult : Fin 51 → Nat := ![8749, 46305, 65410, 87534, 53206, 64498, 189091, 1540, 56064, 195880, 21848, 87092, 40413, 118537, 147179, 75861, 66682, 66514, 23388, 8487, 97486, 4687, 17271, 31770, 10261, 31591, 33111, 82279, 41051, 23196, 41585, 7009, 66846, 8408, 23572, 6435, 63949, 301348, 73303, 6285, 110684, 79483, 94254, 15834, 103424, 268237, 278152, 551618, 105468, 259763, 301348]

theorem plane453GenLeaf0002 (x : Fin 50 → Int)
    (hroot : plane453GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hUB_35 : x 35 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (1 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane453GenLeaf0002Refs i).resolveCoeff plane453GenOccSys j)
    (fun i => (plane453GenLeaf0002Refs i).resolveRhs plane453GenOccSys) plane453GenLeaf0002Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane453GenLeaf0002Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 30
  · exact hroot.hOcc 35
  · exact hroot.hOcc 38
  · exact hroot.hOcc 46
  · exact hroot.hOcc 48
  · exact hroot.hOcc 52
  · exact hroot.hOcc 56
  · exact hroot.hOcc 58
  · exact hroot.hOcc 62
  · exact hroot.hOcc 68
  · exact hroot.hOcc 81
  · exact hroot.hOcc 85
  · exact hroot.hOcc 94
  · exact hroot.hOcc 103
  · exact hroot.hOcc 104
  · exact hroot.hOcc 105
  · exact hroot.hOcc 108
  · exact hroot.hOcc 116
  · exact hroot.hOcc 133
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 139
  · exact hroot.hOcc 150
  · exact hroot.hOcc 156
  · exact hroot.hOcc 159
  · exact hroot.hOcc 161
  · exact hroot.hOcc 163
  · exact hroot.hOcc 168
  · exact hroot.hOcc 172
  · exact hroot.hOcc 179
  · exact hroot.hOcc 181
  · exact hroot.hOcc 185
  · exact hroot.hOcc 187
  · exact hroot.hOcc 193
  · exact hroot.hOcc 199
  · exact hroot.hOcc 209
  · change (∑ j, (-1 : Int) * x j) ≤ -plane453GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (22 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (23 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (25 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (28 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (39 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (48 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (35 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (5 : Fin 50) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (15 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (1 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (17 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (11 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11

end QiushiMatmul
