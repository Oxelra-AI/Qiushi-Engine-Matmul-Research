import QiushiPlane485GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane485GenLeaf0001Refs : Fin 42 → RowRef 421 41 := ![.occ 87, .occ 90, .occ 95, .occ 106, .occ 110, .occ 117, .occ 132, .occ 133, .occ 134, .occ 135, .occ 136, .occ 150, .occ 163, .occ 170, .occ 175, .occ 182, .occ 203, .occ 231, .occ 233, .occ 244, .occ 248, .occ 262, .occ 278, .occ 287, .occ 297, .occ 308, .occ 356, .occ 363, .occ 366, .occ 381, .occ 384, .occ 401, .occ 403, .sumGe, .branchLe 28 (0), .branchLe 21 (0), .branchLe 14 (0), .branchLe 11 (0), .branchLe 39 (0), .branchLe 17 (0), .branchGe 10 (1), .branchLe 24 (0)]

def plane485GenLeaf0001Mult : Fin 42 → Nat := ![22346, 12034, 4108, 3600, 376, 1494, 703, 11721, 5188, 17243, 1321, 2422, 1318, 4144, 13644, 802, 976, 618, 952, 4010, 10430, 14828, 15820, 8478, 4760, 12348, 4722, 2960, 1776, 874, 7674, 5230, 978, 33742, 18434, 26560, 31092, 10456, 33742, 28512, 64162, 32940]

theorem plane485GenLeaf0001 (x : Fin 41 → Int)
    (hroot : plane485GenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane485GenLeaf0001Refs i).resolveCoeff plane485GenOccSys j)
    (fun i => (plane485GenLeaf0001Refs i).resolveRhs plane485GenOccSys) plane485GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane485GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 90
  · exact hroot.hOcc 95
  · exact hroot.hOcc 106
  · exact hroot.hOcc 110
  · exact hroot.hOcc 117
  · exact hroot.hOcc 132
  · exact hroot.hOcc 133
  · exact hroot.hOcc 134
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 150
  · exact hroot.hOcc 163
  · exact hroot.hOcc 170
  · exact hroot.hOcc 175
  · exact hroot.hOcc 182
  · exact hroot.hOcc 203
  · exact hroot.hOcc 231
  · exact hroot.hOcc 233
  · exact hroot.hOcc 244
  · exact hroot.hOcc 248
  · exact hroot.hOcc 262
  · exact hroot.hOcc 278
  · exact hroot.hOcc 287
  · exact hroot.hOcc 297
  · exact hroot.hOcc 308
  · exact hroot.hOcc 356
  · exact hroot.hOcc 363
  · exact hroot.hOcc 366
  · exact hroot.hOcc 381
  · exact hroot.hOcc 384
  · exact hroot.hOcc 401
  · exact hroot.hOcc 403
  · change (∑ j, (-1 : Int) * x j) ≤ -plane485GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (28 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (21 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (14 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (11 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (39 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (17 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (10 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10
  · change (∑ k, (if k = (24 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24

end QiushiMatmul
