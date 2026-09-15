import QiushiPlane462GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane462GenLeaf0015Refs : Fin 63 → RowRef 294 62 := ![.occ 2, .occ 6, .occ 20, .occ 25, .occ 30, .occ 34, .occ 35, .occ 41, .occ 45, .occ 47, .occ 49, .occ 57, .occ 61, .occ 62, .occ 67, .occ 68, .occ 72, .occ 77, .occ 81, .occ 86, .occ 88, .occ 91, .occ 96, .occ 97, .occ 99, .occ 100, .occ 103, .occ 109, .occ 110, .occ 113, .occ 122, .occ 141, .occ 152, .occ 156, .occ 160, .occ 169, .occ 174, .occ 186, .occ 193, .occ 195, .occ 200, .occ 206, .occ 224, .occ 257, .occ 260, .occ 278, .occ 284, .occ 286, .sumGe, .nonneg 0, .nonneg 8, .nonneg 17, .nonneg 50, .nonneg 52, .nonneg 57, .nonneg 59, .nonneg 61, .branchGe 3 (1), .branchGe 5 (1), .branchGe 24 (1), .branchGe 27 (1), .branchLe 9 (0), .branchLe 16 (0)]

def plane462GenLeaf0015Mult : Fin 63 → Nat := ![18104, 277756, 1976184, 3228660, 1587448, 2620920, 4815898, 657608, 1104032, 1261436, 162972, 1245584, 1034744, 343008, 1622242, 2070752, 676314, 1572076, 1205514, 50258, 1812698, 1103790, 1314053, 1821479, 2385968, 1034978, 2344030, 1360839, 1544393, 195598, 1055954, 1576878, 62508, 511174, 1028242, 1543554, 507944, 1392874, 1477870, 199358, 2401946, 805132, 1392874, 552494, 1694284, 1489958, 695572, 2485994, 9393014, 7137390, 10275396, 462694, 279620, 1221036, 3361016, 1938948, 2886516, 2187208, 15937754, 3052506, 14571546, 8885070, 9393014]

theorem plane462GenLeaf0015 (x : Fin 62 → Int)
    (hroot : plane462GenOccSys.RootHolds x)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane462GenLeaf0015Refs i).resolveCoeff plane462GenOccSys j)
    (fun i => (plane462GenLeaf0015Refs i).resolveRhs plane462GenOccSys) plane462GenLeaf0015Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane462GenLeaf0015Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · exact hroot.hOcc 6
  · exact hroot.hOcc 20
  · exact hroot.hOcc 25
  · exact hroot.hOcc 30
  · exact hroot.hOcc 34
  · exact hroot.hOcc 35
  · exact hroot.hOcc 41
  · exact hroot.hOcc 45
  · exact hroot.hOcc 47
  · exact hroot.hOcc 49
  · exact hroot.hOcc 57
  · exact hroot.hOcc 61
  · exact hroot.hOcc 62
  · exact hroot.hOcc 67
  · exact hroot.hOcc 68
  · exact hroot.hOcc 72
  · exact hroot.hOcc 77
  · exact hroot.hOcc 81
  · exact hroot.hOcc 86
  · exact hroot.hOcc 88
  · exact hroot.hOcc 91
  · exact hroot.hOcc 96
  · exact hroot.hOcc 97
  · exact hroot.hOcc 99
  · exact hroot.hOcc 100
  · exact hroot.hOcc 103
  · exact hroot.hOcc 109
  · exact hroot.hOcc 110
  · exact hroot.hOcc 113
  · exact hroot.hOcc 122
  · exact hroot.hOcc 141
  · exact hroot.hOcc 152
  · exact hroot.hOcc 156
  · exact hroot.hOcc 160
  · exact hroot.hOcc 169
  · exact hroot.hOcc 174
  · exact hroot.hOcc 186
  · exact hroot.hOcc 193
  · exact hroot.hOcc 195
  · exact hroot.hOcc 200
  · exact hroot.hOcc 206
  · exact hroot.hOcc 224
  · exact hroot.hOcc 257
  · exact hroot.hOcc 260
  · exact hroot.hOcc 278
  · exact hroot.hOcc 284
  · exact hroot.hOcc 286
  · change (∑ j, (-1 : Int) * x j) ≤ -plane462GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (8 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (17 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (50 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (52 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (57 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 57
  · change (∑ k, (if k = (59 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (61 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 61
  · change (∑ k, (if k = (3 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3
  · change (∑ k, (if k = (5 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5
  · change (∑ k, (if k = (24 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24
  · change (∑ k, (if k = (27 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (9 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (16 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16

end QiushiMatmul
