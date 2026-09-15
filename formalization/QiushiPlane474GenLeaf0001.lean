import QiushiPlane474GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane474GenLeaf0001Refs : Fin 61 → RowRef 146 60 := ![.occ 9, .occ 10, .occ 11, .occ 12, .occ 21, .occ 24, .occ 28, .occ 31, .occ 36, .occ 38, .occ 39, .occ 42, .occ 46, .occ 48, .occ 50, .occ 51, .occ 52, .occ 53, .occ 59, .occ 61, .occ 63, .occ 64, .occ 65, .occ 66, .occ 74, .occ 76, .occ 77, .occ 82, .occ 83, .occ 90, .occ 95, .occ 101, .occ 110, .occ 111, .occ 115, .occ 118, .occ 120, .occ 122, .occ 127, .occ 131, .occ 132, .occ 133, .occ 135, .occ 136, .occ 138, .occ 141, .occ 144, .sumGe, .nonneg 9, .nonneg 14, .nonneg 17, .nonneg 25, .nonneg 26, .nonneg 38, .nonneg 45, .nonneg 52, .nonneg 53, .branchLe 44 (0), .branchLe 43 (0), .branchLe 22 (0), .branchGe 37 (1)]

def plane474GenLeaf0001Mult : Fin 61 → Nat := ![304331, 3028124, 2764291, 2530341, 567292, 4104985, 2637810, 1361849, 3407278, 3152153, 380811, 1239099, 335772, 2324392, 3878616, 1632005, 3208029, 3105219, 1788300, 789777, 3055578, 2404535, 1497729, 2326685, 1208002, 739601, 1126978, 3854923, 872786, 1043311, 825367, 310290, 754917, 162252, 2003015, 1403599, 1002650, 340430, 1655711, 244523, 177859, 844543, 482689, 1307544, 672480, 1072949, 1072949, 9046296, 2528843, 995393, 1044948, 526063, 395025, 1084534, 3579889, 5774533, 224711, 7632917, 6227918, 5969281, 22584607]

theorem plane474GenLeaf0001 (x : Fin 60 → Int)
    (hroot : plane474GenOccSys.RootHolds x)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_43 : x 43 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane474GenLeaf0001Refs i).resolveCoeff plane474GenOccSys j)
    (fun i => (plane474GenLeaf0001Refs i).resolveRhs plane474GenOccSys) plane474GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane474GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 9
  · exact hroot.hOcc 10
  · exact hroot.hOcc 11
  · exact hroot.hOcc 12
  · exact hroot.hOcc 21
  · exact hroot.hOcc 24
  · exact hroot.hOcc 28
  · exact hroot.hOcc 31
  · exact hroot.hOcc 36
  · exact hroot.hOcc 38
  · exact hroot.hOcc 39
  · exact hroot.hOcc 42
  · exact hroot.hOcc 46
  · exact hroot.hOcc 48
  · exact hroot.hOcc 50
  · exact hroot.hOcc 51
  · exact hroot.hOcc 52
  · exact hroot.hOcc 53
  · exact hroot.hOcc 59
  · exact hroot.hOcc 61
  · exact hroot.hOcc 63
  · exact hroot.hOcc 64
  · exact hroot.hOcc 65
  · exact hroot.hOcc 66
  · exact hroot.hOcc 74
  · exact hroot.hOcc 76
  · exact hroot.hOcc 77
  · exact hroot.hOcc 82
  · exact hroot.hOcc 83
  · exact hroot.hOcc 90
  · exact hroot.hOcc 95
  · exact hroot.hOcc 101
  · exact hroot.hOcc 110
  · exact hroot.hOcc 111
  · exact hroot.hOcc 115
  · exact hroot.hOcc 118
  · exact hroot.hOcc 120
  · exact hroot.hOcc 122
  · exact hroot.hOcc 127
  · exact hroot.hOcc 131
  · exact hroot.hOcc 132
  · exact hroot.hOcc 133
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 138
  · exact hroot.hOcc 141
  · exact hroot.hOcc 144
  · change (∑ j, (-1 : Int) * x j) ≤ -plane474GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (9 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 9
  · change (∑ k, (if k = (14 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (17 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (25 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (26 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (38 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (45 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (52 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (53 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (44 : Fin 60) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (43 : Fin 60) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (22 : Fin 60) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (37 : Fin 60) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37

end QiushiMatmul
