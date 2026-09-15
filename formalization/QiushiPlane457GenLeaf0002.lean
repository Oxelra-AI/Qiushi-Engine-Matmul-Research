import QiushiPlane457GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane457GenLeaf0002Refs : Fin 50 → RowRef 178 49 := ![.occ 14, .occ 16, .occ 19, .occ 24, .occ 28, .occ 33, .occ 42, .occ 58, .occ 65, .occ 68, .occ 73, .occ 74, .occ 75, .occ 77, .occ 78, .occ 79, .occ 91, .occ 92, .occ 95, .occ 96, .occ 106, .occ 112, .occ 118, .occ 122, .occ 128, .occ 132, .occ 134, .occ 136, .occ 140, .occ 142, .occ 144, .occ 145, .occ 147, .occ 152, .occ 154, .occ 155, .occ 160, .occ 163, .occ 168, .occ 169, .occ 171, .occ 172, .sumGe, .nonneg 6, .nonneg 18, .nonneg 22, .nonneg 27, .nonneg 29, .branchLe 3 (0), .branchGe 1 (1)]

def plane457GenLeaf0002Mult : Fin 50 → Nat := ![1156643, 34698, 2989800, 502252, 132568, 900190, 340188, 236658, 4275665, 4423747, 955747, 832411, 3885040, 1286693, 1249269, 342339, 1424070, 3047065, 1976722, 2674689, 2573559, 1577387, 2132668, 407885, 1351122, 1502, 147502, 2454866, 212535, 111856, 1220736, 498406, 458703, 115105, 1086246, 181011, 823907, 336320, 699304, 630795, 914534, 199097, 7031264, 1378982, 1444195, 391139, 1119123, 15275, 7031264, 17890779]

theorem plane457GenLeaf0002 (x : Fin 49 → Int)
    (hroot : plane457GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hUB_3 : x 3 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane457GenLeaf0002Refs i).resolveCoeff plane457GenOccSys j)
    (fun i => (plane457GenLeaf0002Refs i).resolveRhs plane457GenOccSys) plane457GenLeaf0002Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane457GenLeaf0002Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 14
  · exact hroot.hOcc 16
  · exact hroot.hOcc 19
  · exact hroot.hOcc 24
  · exact hroot.hOcc 28
  · exact hroot.hOcc 33
  · exact hroot.hOcc 42
  · exact hroot.hOcc 58
  · exact hroot.hOcc 65
  · exact hroot.hOcc 68
  · exact hroot.hOcc 73
  · exact hroot.hOcc 74
  · exact hroot.hOcc 75
  · exact hroot.hOcc 77
  · exact hroot.hOcc 78
  · exact hroot.hOcc 79
  · exact hroot.hOcc 91
  · exact hroot.hOcc 92
  · exact hroot.hOcc 95
  · exact hroot.hOcc 96
  · exact hroot.hOcc 106
  · exact hroot.hOcc 112
  · exact hroot.hOcc 118
  · exact hroot.hOcc 122
  · exact hroot.hOcc 128
  · exact hroot.hOcc 132
  · exact hroot.hOcc 134
  · exact hroot.hOcc 136
  · exact hroot.hOcc 140
  · exact hroot.hOcc 142
  · exact hroot.hOcc 144
  · exact hroot.hOcc 145
  · exact hroot.hOcc 147
  · exact hroot.hOcc 152
  · exact hroot.hOcc 154
  · exact hroot.hOcc 155
  · exact hroot.hOcc 160
  · exact hroot.hOcc 163
  · exact hroot.hOcc 168
  · exact hroot.hOcc 169
  · exact hroot.hOcc 171
  · exact hroot.hOcc 172
  · change (∑ j, (-1 : Int) * x j) ≤ -plane457GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (18 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (22 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (27 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27
  · change (∑ k, (if k = (29 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (3 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (1 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1

end QiushiMatmul
