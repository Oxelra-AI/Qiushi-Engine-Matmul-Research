import QiushiPlane462GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane462GenLeaf0020Refs : Fin 63 → RowRef 294 62 := ![.occ 14, .occ 30, .occ 34, .occ 35, .occ 42, .occ 46, .occ 47, .occ 63, .occ 67, .occ 74, .occ 76, .occ 78, .occ 80, .occ 81, .occ 84, .occ 85, .occ 86, .occ 88, .occ 92, .occ 96, .occ 100, .occ 103, .occ 105, .occ 165, .occ 175, .occ 193, .occ 211, .occ 212, .occ 216, .occ 226, .occ 231, .occ 232, .occ 243, .occ 244, .occ 251, .occ 258, .occ 260, .occ 261, .occ 268, .occ 279, .occ 286, .occ 287, .occ 292, .sumGe, .nonneg 0, .nonneg 7, .nonneg 8, .nonneg 10, .nonneg 12, .nonneg 19, .nonneg 38, .nonneg 40, .nonneg 42, .nonneg 47, .nonneg 48, .nonneg 57, .nonneg 59, .branchGe 3 (1), .branchGe 24 (1), .branchGe 27 (1), .branchGe 9 (1), .branchLe 6 (0), .branchGe 34 (2)]

def plane462GenLeaf0020Mult : Fin 63 → Nat := ![1433437, 71368, 2139392, 1838346, 1028844, 2441812, 2610516, 830112, 1430313, 915056, 1145116, 760134, 1573957, 1569344, 3091250, 1184377, 1091182, 2196872, 1320298, 2059333, 3051927, 1690331, 445692, 943306, 2868640, 2110408, 742030, 717218, 208902, 893954, 916780, 462122, 280504, 1787333, 424448, 274770, 1628359, 62578, 982333, 288540, 1157093, 1997889, 713580, 8394740, 3703412, 6885974, 10667188, 133412, 1749906, 990036, 6103252, 7107540, 255624, 51240, 829136, 1397924, 1418732, 5874568, 1988702, 6519746, 3004066, 8394740, 14546840]

theorem plane462GenLeaf0020 (x : Fin 62 → Int)
    (hroot : plane462GenOccSys.RootHolds x)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hLB_34 : (2 : Int) ≤ x 34)
    (hUB_6 : x 6 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane462GenLeaf0020Refs i).resolveCoeff plane462GenOccSys j)
    (fun i => (plane462GenLeaf0020Refs i).resolveRhs plane462GenOccSys) plane462GenLeaf0020Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane462GenLeaf0020Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 14
  · exact hroot.hOcc 30
  · exact hroot.hOcc 34
  · exact hroot.hOcc 35
  · exact hroot.hOcc 42
  · exact hroot.hOcc 46
  · exact hroot.hOcc 47
  · exact hroot.hOcc 63
  · exact hroot.hOcc 67
  · exact hroot.hOcc 74
  · exact hroot.hOcc 76
  · exact hroot.hOcc 78
  · exact hroot.hOcc 80
  · exact hroot.hOcc 81
  · exact hroot.hOcc 84
  · exact hroot.hOcc 85
  · exact hroot.hOcc 86
  · exact hroot.hOcc 88
  · exact hroot.hOcc 92
  · exact hroot.hOcc 96
  · exact hroot.hOcc 100
  · exact hroot.hOcc 103
  · exact hroot.hOcc 105
  · exact hroot.hOcc 165
  · exact hroot.hOcc 175
  · exact hroot.hOcc 193
  · exact hroot.hOcc 211
  · exact hroot.hOcc 212
  · exact hroot.hOcc 216
  · exact hroot.hOcc 226
  · exact hroot.hOcc 231
  · exact hroot.hOcc 232
  · exact hroot.hOcc 243
  · exact hroot.hOcc 244
  · exact hroot.hOcc 251
  · exact hroot.hOcc 258
  · exact hroot.hOcc 260
  · exact hroot.hOcc 261
  · exact hroot.hOcc 268
  · exact hroot.hOcc 279
  · exact hroot.hOcc 286
  · exact hroot.hOcc 287
  · exact hroot.hOcc 292
  · change (∑ j, (-1 : Int) * x j) ≤ -plane462GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (7 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (8 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (10 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (12 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (19 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (38 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (40 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (42 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (47 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (48 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (57 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 57
  · change (∑ k, (if k = (59 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (3 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3
  · change (∑ k, (if k = (24 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24
  · change (∑ k, (if k = (27 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (9 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9
  · change (∑ k, (if k = (6 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (34 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34

end QiushiMatmul
