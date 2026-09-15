import QiushiPlane469GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane469GenLeaf0003Refs : Fin 61 → RowRef 217 60 := ![.occ 18, .occ 19, .occ 21, .occ 23, .occ 25, .occ 30, .occ 31, .occ 41, .occ 43, .occ 45, .occ 46, .occ 51, .occ 57, .occ 58, .occ 69, .occ 71, .occ 82, .occ 83, .occ 84, .occ 96, .occ 99, .occ 113, .occ 115, .occ 122, .occ 123, .occ 125, .occ 128, .occ 129, .occ 131, .occ 133, .occ 139, .occ 144, .occ 149, .occ 150, .occ 151, .occ 160, .occ 163, .occ 165, .occ 170, .occ 188, .occ 190, .occ 199, .occ 202, .occ 203, .occ 207, .occ 208, .occ 209, .occ 213, .occ 214, .sumGe, .nonneg 8, .nonneg 17, .nonneg 32, .nonneg 33, .nonneg 41, .nonneg 52, .branchLe 34 (0), .branchLe 13 (0), .branchLe 54 (0), .branchLe 40 (0), .branchGe 45 (1)]

def plane469GenLeaf0003Mult : Fin 61 → Nat := ![117536, 139072, 94072, 70064, 339192, 89100, 25060, 59144, 144600, 187408, 138832, 200536, 518280, 83524, 301324, 1206976, 241088, 222968, 107104, 337784, 103036, 164028, 147304, 93928, 106004, 31764, 94280, 63526, 197756, 17792, 148406, 119400, 143386, 2324, 16178, 46290, 119976, 96938, 12578, 172572, 135288, 50156, 273167, 176769, 151466, 449612, 361180, 171155, 155785, 1626248, 258596, 445176, 105504, 140820, 488332, 471980, 945828, 714408, 1296176, 1049372, 2433948]

theorem plane469GenLeaf0003 (x : Fin 60 → Int)
    (hroot : plane469GenOccSys.RootHolds x)
    (hLB_45 : (1 : Int) ≤ x 45)
    (hUB_34 : x 34 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_54 : x 54 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane469GenLeaf0003Refs i).resolveCoeff plane469GenOccSys j)
    (fun i => (plane469GenLeaf0003Refs i).resolveRhs plane469GenOccSys) plane469GenLeaf0003Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane469GenLeaf0003Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 18
  · exact hroot.hOcc 19
  · exact hroot.hOcc 21
  · exact hroot.hOcc 23
  · exact hroot.hOcc 25
  · exact hroot.hOcc 30
  · exact hroot.hOcc 31
  · exact hroot.hOcc 41
  · exact hroot.hOcc 43
  · exact hroot.hOcc 45
  · exact hroot.hOcc 46
  · exact hroot.hOcc 51
  · exact hroot.hOcc 57
  · exact hroot.hOcc 58
  · exact hroot.hOcc 69
  · exact hroot.hOcc 71
  · exact hroot.hOcc 82
  · exact hroot.hOcc 83
  · exact hroot.hOcc 84
  · exact hroot.hOcc 96
  · exact hroot.hOcc 99
  · exact hroot.hOcc 113
  · exact hroot.hOcc 115
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 125
  · exact hroot.hOcc 128
  · exact hroot.hOcc 129
  · exact hroot.hOcc 131
  · exact hroot.hOcc 133
  · exact hroot.hOcc 139
  · exact hroot.hOcc 144
  · exact hroot.hOcc 149
  · exact hroot.hOcc 150
  · exact hroot.hOcc 151
  · exact hroot.hOcc 160
  · exact hroot.hOcc 163
  · exact hroot.hOcc 165
  · exact hroot.hOcc 170
  · exact hroot.hOcc 188
  · exact hroot.hOcc 190
  · exact hroot.hOcc 199
  · exact hroot.hOcc 202
  · exact hroot.hOcc 203
  · exact hroot.hOcc 207
  · exact hroot.hOcc 208
  · exact hroot.hOcc 209
  · exact hroot.hOcc 213
  · exact hroot.hOcc 214
  · change (∑ j, (-1 : Int) * x j) ≤ -plane469GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (17 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (32 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (33 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (41 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (52 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (34 : Fin 60) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (13 : Fin 60) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (54 : Fin 60) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_54
  · change (∑ k, (if k = (40 : Fin 60) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (45 : Fin 60) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_45

end QiushiMatmul
