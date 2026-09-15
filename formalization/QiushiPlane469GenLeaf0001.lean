import QiushiPlane469GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane469GenLeaf0001Refs : Fin 61 → RowRef 217 60 := ![.occ 6, .occ 9, .occ 10, .occ 15, .occ 18, .occ 19, .occ 24, .occ 43, .occ 48, .occ 53, .occ 57, .occ 58, .occ 69, .occ 71, .occ 72, .occ 77, .occ 81, .occ 82, .occ 83, .occ 89, .occ 94, .occ 96, .occ 98, .occ 99, .occ 110, .occ 111, .occ 112, .occ 122, .occ 128, .occ 129, .occ 134, .occ 137, .occ 138, .occ 139, .occ 140, .occ 141, .occ 179, .occ 185, .occ 193, .occ 194, .occ 201, .occ 202, .occ 207, .occ 209, .occ 214, .sumGe, .nonneg 3, .nonneg 10, .nonneg 17, .nonneg 32, .nonneg 41, .nonneg 45, .nonneg 46, .nonneg 52, .branchLe 34 (0), .branchLe 13 (0), .branchLe 8 (0), .branchLe 54 (0), .branchLe 40 (0), .branchGe 5 (1), .branchLe 31 (0)]

def plane469GenLeaf0001Mult : Fin 61 → Nat := ![2748488, 330661, 8376484, 9526706, 5129246, 4592343, 3454676, 1924748, 8188684, 7370427, 14829445, 13231326, 4447292, 8119842, 2047803, 607267, 4489387, 5130659, 11706147, 9050780, 5056019, 8307976, 1139518, 5911931, 989437, 4763452, 534759, 1501583, 8875450, 1471528, 3329617, 151475, 4022857, 3851613, 1546545, 1519420, 4478056, 3705468, 3490888, 906302, 1633646, 6023639, 7891463, 5814831, 1855840, 34394667, 14358631, 39533, 22242698, 3917194, 23189659, 759462, 12465979, 8994935, 18430580, 28060771, 6706113, 22688520, 28371028, 22123296, 29947375]

theorem plane469GenLeaf0001 (x : Fin 60 → Int)
    (hroot : plane469GenOccSys.RootHolds x)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hUB_34 : x 34 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_54 : x 54 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    (hUB_45 : x 45 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane469GenLeaf0001Refs i).resolveCoeff plane469GenOccSys j)
    (fun i => (plane469GenLeaf0001Refs i).resolveRhs plane469GenOccSys) plane469GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane469GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 6
  · exact hroot.hOcc 9
  · exact hroot.hOcc 10
  · exact hroot.hOcc 15
  · exact hroot.hOcc 18
  · exact hroot.hOcc 19
  · exact hroot.hOcc 24
  · exact hroot.hOcc 43
  · exact hroot.hOcc 48
  · exact hroot.hOcc 53
  · exact hroot.hOcc 57
  · exact hroot.hOcc 58
  · exact hroot.hOcc 69
  · exact hroot.hOcc 71
  · exact hroot.hOcc 72
  · exact hroot.hOcc 77
  · exact hroot.hOcc 81
  · exact hroot.hOcc 82
  · exact hroot.hOcc 83
  · exact hroot.hOcc 89
  · exact hroot.hOcc 94
  · exact hroot.hOcc 96
  · exact hroot.hOcc 98
  · exact hroot.hOcc 99
  · exact hroot.hOcc 110
  · exact hroot.hOcc 111
  · exact hroot.hOcc 112
  · exact hroot.hOcc 122
  · exact hroot.hOcc 128
  · exact hroot.hOcc 129
  · exact hroot.hOcc 134
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 141
  · exact hroot.hOcc 179
  · exact hroot.hOcc 185
  · exact hroot.hOcc 193
  · exact hroot.hOcc 194
  · exact hroot.hOcc 201
  · exact hroot.hOcc 202
  · exact hroot.hOcc 207
  · exact hroot.hOcc 209
  · exact hroot.hOcc 214
  · change (∑ j, (-1 : Int) * x j) ≤ -plane469GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (10 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (17 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (32 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (41 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (45 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (46 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (52 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (34 : Fin 60) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (13 : Fin 60) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (8 : Fin 60) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (54 : Fin 60) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_54
  · change (∑ k, (if k = (40 : Fin 60) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (5 : Fin 60) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5
  · change (∑ k, (if k = (31 : Fin 60) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31

end QiushiMatmul
