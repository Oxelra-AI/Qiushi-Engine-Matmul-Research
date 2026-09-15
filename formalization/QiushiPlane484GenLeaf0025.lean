import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0025Refs : Fin 44 → RowRef 1665 43 := ![.occ 121, .occ 122, .occ 127, .occ 128, .occ 131, .occ 134, .occ 138, .occ 139, .occ 140, .occ 633, .occ 682, .occ 987, .occ 1124, .occ 1150, .occ 1165, .occ 1170, .occ 1186, .occ 1206, .occ 1213, .occ 1216, .occ 1220, .occ 1233, .occ 1263, .occ 1266, .occ 1274, .occ 1357, .occ 1500, .occ 1512, .occ 1513, .occ 1597, .occ 1633, .sumGe, .nonneg 5, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchLe 17 (0), .branchGe 35 (1), .branchLe 25 (0), .branchLe 42 (0), .branchGe 19 (1), .branchGe 1 (1)]

def plane484GenLeaf0025Mult : Fin 44 → Nat := ![50727, 73397, 88247, 97439, 184874, 70544, 19374, 132472, 2060, 58064, 79664, 48840, 43608, 131732, 812, 23834, 145126, 28996, 28996, 4120, 139328, 35990, 32074, 64748, 12740, 68484, 32978, 33562, 12356, 157248, 36440, 421452, 24392, 72604, 220512, 417332, 128076, 297328, 390396, 317992, 317792, 385012, 812896, 484014]

theorem plane484GenLeaf0025 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0025Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0025Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0025Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0025Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 127
  · exact hroot.hOcc 128
  · exact hroot.hOcc 131
  · exact hroot.hOcc 134
  · exact hroot.hOcc 138
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 633
  · exact hroot.hOcc 682
  · exact hroot.hOcc 987
  · exact hroot.hOcc 1124
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1165
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1233
  · exact hroot.hOcc 1263
  · exact hroot.hOcc 1266
  · exact hroot.hOcc 1274
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1500
  · exact hroot.hOcc 1512
  · exact hroot.hOcc 1513
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1633
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1

end QiushiMatmul
