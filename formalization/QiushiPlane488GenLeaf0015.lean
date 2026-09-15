import QiushiPlane488GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane488GenLeaf0015Refs : Fin 42 → RowRef 413 41 := ![.occ 90, .occ 96, .occ 107, .occ 109, .occ 112, .occ 131, .occ 137, .occ 159, .occ 164, .occ 165, .occ 170, .occ 174, .occ 184, .occ 190, .occ 194, .occ 195, .occ 200, .occ 210, .occ 231, .occ 232, .occ 259, .occ 262, .occ 264, .occ 274, .occ 285, .occ 289, .occ 306, .occ 344, .occ 349, .occ 352, .occ 362, .occ 366, .occ 368, .occ 379, .occ 395, .sumGe, .nonneg 7, .branchLe 27 (0), .branchLe 15 (0), .branchGe 20 (1), .branchLe 39 (0), .branchLe 31 (0)]

def plane488GenLeaf0015Mult : Fin 42 → Nat := ![647, 4921, 2737, 1418, 3889, 276, 5413, 1523, 2161, 2657, 2203, 4423, 454, 1912, 2081, 314, 530, 1652, 1288, 3518, 2674, 140, 1334, 175, 513, 752, 1705, 1100, 219, 641, 1595, 937, 178, 1319, 1503, 8399, 1141, 6797, 8259, 25997, 6896, 8399]

theorem plane488GenLeaf0015 (x : Fin 41 → Int)
    (hroot : plane488GenOccSys.RootHolds x)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane488GenLeaf0015Refs i).resolveCoeff plane488GenOccSys j)
    (fun i => (plane488GenLeaf0015Refs i).resolveRhs plane488GenOccSys) plane488GenLeaf0015Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane488GenLeaf0015Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 90
  · exact hroot.hOcc 96
  · exact hroot.hOcc 107
  · exact hroot.hOcc 109
  · exact hroot.hOcc 112
  · exact hroot.hOcc 131
  · exact hroot.hOcc 137
  · exact hroot.hOcc 159
  · exact hroot.hOcc 164
  · exact hroot.hOcc 165
  · exact hroot.hOcc 170
  · exact hroot.hOcc 174
  · exact hroot.hOcc 184
  · exact hroot.hOcc 190
  · exact hroot.hOcc 194
  · exact hroot.hOcc 195
  · exact hroot.hOcc 200
  · exact hroot.hOcc 210
  · exact hroot.hOcc 231
  · exact hroot.hOcc 232
  · exact hroot.hOcc 259
  · exact hroot.hOcc 262
  · exact hroot.hOcc 264
  · exact hroot.hOcc 274
  · exact hroot.hOcc 285
  · exact hroot.hOcc 289
  · exact hroot.hOcc 306
  · exact hroot.hOcc 344
  · exact hroot.hOcc 349
  · exact hroot.hOcc 352
  · exact hroot.hOcc 362
  · exact hroot.hOcc 366
  · exact hroot.hOcc 368
  · exact hroot.hOcc 379
  · exact hroot.hOcc 395
  · change (∑ j, (-1 : Int) * x j) ≤ -plane488GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (27 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (15 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (20 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20
  · change (∑ k, (if k = (39 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (31 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31

end QiushiMatmul
