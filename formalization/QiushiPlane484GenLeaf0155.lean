import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0155Refs : Fin 44 → RowRef 1665 43 := ![.occ 121, .occ 127, .occ 491, .occ 716, .occ 723, .occ 727, .occ 729, .occ 750, .occ 770, .occ 777, .occ 784, .occ 1154, .occ 1164, .occ 1269, .occ 1370, .occ 1380, .occ 1402, .occ 1404, .occ 1405, .occ 1408, .occ 1421, .occ 1427, .occ 1436, .occ 1447, .occ 1448, .occ 1471, .occ 1532, .occ 1635, .occ 1647, .occ 1653, .occ 1655, .occ 1664, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchGe 7 (1), .branchLe 18 (0), .branchLe 30 (0), .branchLe 21 (0), .branchGe 42 (1), .branchLe 0 (0), .branchLe 26 (0)]

def plane484GenLeaf0155Mult : Fin 44 → Nat := ![12676, 7858, 3786, 12472, 5200, 7640, 1682, 1040, 3246, 10230, 9896, 520, 7902, 170, 4093, 6278, 835, 4948, 4361, 4233, 5396, 4783, 5170, 4503, 3034, 3356, 1776, 2328, 2562, 3431, 387, 1904, 28228, 20986, 23338, 66814, 28228, 44848, 12728, 7806, 28228, 78400, 18422, 23058]

theorem plane484GenLeaf0155 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0155Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0155Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0155Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0155Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 127
  · exact hroot.hOcc 491
  · exact hroot.hOcc 716
  · exact hroot.hOcc 723
  · exact hroot.hOcc 727
  · exact hroot.hOcc 729
  · exact hroot.hOcc 750
  · exact hroot.hOcc 770
  · exact hroot.hOcc 777
  · exact hroot.hOcc 784
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1269
  · exact hroot.hOcc 1370
  · exact hroot.hOcc 1380
  · exact hroot.hOcc 1402
  · exact hroot.hOcc 1404
  · exact hroot.hOcc 1405
  · exact hroot.hOcc 1408
  · exact hroot.hOcc 1421
  · exact hroot.hOcc 1427
  · exact hroot.hOcc 1436
  · exact hroot.hOcc 1447
  · exact hroot.hOcc 1448
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1532
  · exact hroot.hOcc 1635
  · exact hroot.hOcc 1647
  · exact hroot.hOcc 1653
  · exact hroot.hOcc 1655
  · exact hroot.hOcc 1664
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (21 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26

end QiushiMatmul
