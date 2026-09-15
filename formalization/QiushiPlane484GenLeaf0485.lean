import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0485Refs : Fin 37 → RowRef 1665 43 := ![.occ 119, .occ 123, .occ 128, .occ 130, .occ 131, .occ 132, .occ 142, .occ 502, .occ 596, .occ 700, .occ 786, .occ 857, .occ 952, .occ 1054, .occ 1136, .occ 1146, .occ 1154, .occ 1307, .occ 1318, .occ 1358, .occ 1431, .occ 1432, .occ 1564, .occ 1615, .occ 1645, .sumGe, .nonneg 4, .nonneg 12, .nonneg 16, .nonneg 24, .branchGe 15 (1), .branchLe 35 (0), .branchGe 0 (1), .branchLe 19 (0), .branchLe 25 (0), .branchGe 3 (1), .branchGe 8 (1)]

def plane484GenLeaf0485Mult : Fin 37 → Nat := ![38, 31, 37, 1, 29, 6, 12, 3, 8, 25, 2, 13, 3, 2, 28, 3, 1, 4, 2, 4, 9, 19, 2, 6, 4, 38, 39, 111, 13, 1, 100, 38, 86, 9, 6, 194, 124]

theorem plane484GenLeaf0485 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0485Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0485Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0485Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0485Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 123
  · exact hroot.hOcc 128
  · exact hroot.hOcc 130
  · exact hroot.hOcc 131
  · exact hroot.hOcc 132
  · exact hroot.hOcc 142
  · exact hroot.hOcc 502
  · exact hroot.hOcc 596
  · exact hroot.hOcc 700
  · exact hroot.hOcc 786
  · exact hroot.hOcc 857
  · exact hroot.hOcc 952
  · exact hroot.hOcc 1054
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1307
  · exact hroot.hOcc 1318
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1431
  · exact hroot.hOcc 1432
  · exact hroot.hOcc 1564
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1645
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (12 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8

end QiushiMatmul
