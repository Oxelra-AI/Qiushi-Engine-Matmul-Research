import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0564Refs : Fin 43 → RowRef 1665 43 := ![.occ 124, .occ 133, .occ 135, .occ 138, .occ 142, .occ 886, .occ 895, .occ 900, .occ 978, .occ 1071, .occ 1121, .occ 1130, .occ 1213, .occ 1253, .occ 1263, .occ 1266, .occ 1275, .occ 1280, .occ 1293, .occ 1297, .occ 1334, .occ 1340, .occ 1367, .occ 1377, .occ 1393, .occ 1439, .occ 1520, .occ 1527, .occ 1607, .occ 1623, .occ 1651, .sumGe, .nonneg 0, .nonneg 1, .nonneg 20, .nonneg 21, .nonneg 22, .branchGe 15 (1), .branchGe 35 (1), .branchGe 25 (1), .branchLe 29 (0), .branchLe 3 (0), .branchGe 26 (1)]

def plane484GenLeaf0564Mult : Fin 43 → Nat := ![22, 404, 764, 150, 1054, 18, 91, 125, 114, 82, 118, 54, 500, 263, 18, 307, 4, 268, 150, 25, 23, 97, 97, 146, 182, 129, 78, 31, 500, 122, 168, 1054, 676, 18, 4, 1957, 1161, 3122, 1906, 3629, 932, 1000, 2071]

theorem plane484GenLeaf0564 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0564Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0564Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0564Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0564Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 124
  · exact hroot.hOcc 133
  · exact hroot.hOcc 135
  · exact hroot.hOcc 138
  · exact hroot.hOcc 142
  · exact hroot.hOcc 886
  · exact hroot.hOcc 895
  · exact hroot.hOcc 900
  · exact hroot.hOcc 978
  · exact hroot.hOcc 1071
  · exact hroot.hOcc 1121
  · exact hroot.hOcc 1130
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1253
  · exact hroot.hOcc 1263
  · exact hroot.hOcc 1266
  · exact hroot.hOcc 1275
  · exact hroot.hOcc 1280
  · exact hroot.hOcc 1293
  · exact hroot.hOcc 1297
  · exact hroot.hOcc 1334
  · exact hroot.hOcc 1340
  · exact hroot.hOcc 1367
  · exact hroot.hOcc 1377
  · exact hroot.hOcc 1393
  · exact hroot.hOcc 1439
  · exact hroot.hOcc 1520
  · exact hroot.hOcc 1527
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1623
  · exact hroot.hOcc 1651
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26

end QiushiMatmul
