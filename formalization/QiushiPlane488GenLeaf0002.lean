import QiushiPlane488GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane488GenLeaf0002Refs : Fin 40 → RowRef 413 41 := ![.occ 100, .occ 104, .occ 113, .occ 117, .occ 152, .occ 184, .occ 186, .occ 198, .occ 210, .occ 214, .occ 216, .occ 224, .occ 225, .occ 230, .occ 252, .occ 265, .occ 302, .occ 304, .occ 349, .occ 364, .occ 368, .occ 369, .occ 370, .occ 374, .occ 399, .occ 402, .occ 411, .occ 412, .sumGe, .nonneg 7, .nonneg 8, .branchLe 27 (0), .branchLe 15 (0), .branchLe 20 (0), .branchLe 25 (0), .branchLe 13 (0), .branchLe 24 (0), .branchLe 16 (0), .branchLe 4 (0), .branchGe 37 (1)]

def plane488GenLeaf0002Mult : Fin 40 → Nat := ![3612, 5573, 5647, 3382, 5584, 2218, 5573, 6959, 8170, 1991, 19072, 13252, 6014, 2571, 3424, 958, 6640, 4834, 3249, 4687, 3788, 5373, 2010, 2677, 4096, 5089, 1779, 2487, 28427, 5984, 10295, 25940, 21106, 15204, 22441, 8076, 15454, 8434, 12701, 66937]

theorem plane488GenLeaf0002 (x : Fin 41 → Int)
    (hroot : plane488GenOccSys.RootHolds x)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane488GenLeaf0002Refs i).resolveCoeff plane488GenOccSys j)
    (fun i => (plane488GenLeaf0002Refs i).resolveRhs plane488GenOccSys) plane488GenLeaf0002Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane488GenLeaf0002Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 100
  · exact hroot.hOcc 104
  · exact hroot.hOcc 113
  · exact hroot.hOcc 117
  · exact hroot.hOcc 152
  · exact hroot.hOcc 184
  · exact hroot.hOcc 186
  · exact hroot.hOcc 198
  · exact hroot.hOcc 210
  · exact hroot.hOcc 214
  · exact hroot.hOcc 216
  · exact hroot.hOcc 224
  · exact hroot.hOcc 225
  · exact hroot.hOcc 230
  · exact hroot.hOcc 252
  · exact hroot.hOcc 265
  · exact hroot.hOcc 302
  · exact hroot.hOcc 304
  · exact hroot.hOcc 349
  · exact hroot.hOcc 364
  · exact hroot.hOcc 368
  · exact hroot.hOcc 369
  · exact hroot.hOcc 370
  · exact hroot.hOcc 374
  · exact hroot.hOcc 399
  · exact hroot.hOcc 402
  · exact hroot.hOcc 411
  · exact hroot.hOcc 412
  · change (∑ j, (-1 : Int) * x j) ≤ -plane488GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (8 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (27 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (15 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (20 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (25 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (13 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (24 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (16 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (4 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (37 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37

end QiushiMatmul
