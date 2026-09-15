import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0059Refs : Fin 44 → RowRef 1665 43 := ![.occ 121, .occ 123, .occ 255, .occ 256, .occ 385, .occ 612, .occ 708, .occ 960, .occ 1125, .occ 1177, .occ 1190, .occ 1191, .occ 1213, .occ 1260, .occ 1308, .occ 1316, .occ 1319, .occ 1334, .occ 1348, .occ 1353, .occ 1384, .occ 1458, .occ 1532, .occ 1533, .occ 1552, .occ 1562, .occ 1580, .occ 1624, .occ 1628, .occ 1639, .occ 1647, .sumGe, .nonneg 5, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchGe 13 (1), .branchLe 42 (0), .branchLe 0 (0), .branchLe 10 (0), .branchLe 20 (0), .branchGe 36 (1), .branchLe 32 (0)]

def plane484GenLeaf0059Mult : Fin 44 → Nat := ![5480, 132883, 56795, 26337, 29566, 17541, 51402, 10164, 1175, 81765, 10540, 60171, 57698, 14361, 14826, 48168, 82446, 35695, 9300, 33571, 8039, 136429, 53761, 45751, 13441, 14779, 51299, 151432, 48050, 38101, 40050, 411462, 15390, 375767, 129717, 377891, 373361, 605648, 218944, 175057, 357971, 373361, 217877, 360163]

theorem plane484GenLeaf0059 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0059Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0059Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0059Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0059Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 123
  · exact hroot.hOcc 255
  · exact hroot.hOcc 256
  · exact hroot.hOcc 385
  · exact hroot.hOcc 612
  · exact hroot.hOcc 708
  · exact hroot.hOcc 960
  · exact hroot.hOcc 1125
  · exact hroot.hOcc 1177
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1260
  · exact hroot.hOcc 1308
  · exact hroot.hOcc 1316
  · exact hroot.hOcc 1319
  · exact hroot.hOcc 1334
  · exact hroot.hOcc 1348
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1384
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1532
  · exact hroot.hOcc 1533
  · exact hroot.hOcc 1552
  · exact hroot.hOcc 1562
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1624
  · exact hroot.hOcc 1628
  · exact hroot.hOcc 1639
  · exact hroot.hOcc 1647
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (36 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32

end QiushiMatmul
