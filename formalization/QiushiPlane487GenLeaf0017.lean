import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0017Refs : Fin 49 → RowRef 668 48 := ![.occ 83, .occ 85, .occ 92, .occ 122, .occ 150, .occ 155, .occ 168, .occ 233, .occ 235, .occ 257, .occ 269, .occ 280, .occ 288, .occ 292, .occ 297, .occ 303, .occ 308, .occ 315, .occ 370, .occ 377, .occ 380, .occ 386, .occ 391, .occ 393, .occ 399, .occ 402, .occ 447, .occ 448, .occ 450, .occ 488, .occ 508, .occ 521, .occ 523, .occ 524, .occ 598, .occ 604, .occ 607, .occ 609, .occ 651, .occ 656, .occ 666, .sumGe, .nonneg 24, .branchLe 39 (0), .branchLe 23 (0), .branchLe 6 (0), .branchGe 25 (1), .branchLe 1 (0), .branchGe 35 (1)]

def plane487GenLeaf0017Mult : Fin 49 → Nat := ![150548, 250575, 51140, 24026, 44985, 1664, 142967, 369965, 47081, 246568, 97034, 8713, 76576, 27273, 38972, 99951, 22160, 137225, 36430, 38981, 61256, 76804, 259279, 57683, 252369, 212131, 22252, 62398, 18063, 14906, 10989, 41480, 46547, 134308, 240866, 86698, 6136, 7326, 2172, 152816, 93573, 635417, 276664, 394551, 289885, 394551, 1276709, 635417, 1095812]

theorem plane487GenLeaf0017 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0017Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0017Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0017Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0017Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 83
  · exact hroot.hOcc 85
  · exact hroot.hOcc 92
  · exact hroot.hOcc 122
  · exact hroot.hOcc 150
  · exact hroot.hOcc 155
  · exact hroot.hOcc 168
  · exact hroot.hOcc 233
  · exact hroot.hOcc 235
  · exact hroot.hOcc 257
  · exact hroot.hOcc 269
  · exact hroot.hOcc 280
  · exact hroot.hOcc 288
  · exact hroot.hOcc 292
  · exact hroot.hOcc 297
  · exact hroot.hOcc 303
  · exact hroot.hOcc 308
  · exact hroot.hOcc 315
  · exact hroot.hOcc 370
  · exact hroot.hOcc 377
  · exact hroot.hOcc 380
  · exact hroot.hOcc 386
  · exact hroot.hOcc 391
  · exact hroot.hOcc 393
  · exact hroot.hOcc 399
  · exact hroot.hOcc 402
  · exact hroot.hOcc 447
  · exact hroot.hOcc 448
  · exact hroot.hOcc 450
  · exact hroot.hOcc 488
  · exact hroot.hOcc 508
  · exact hroot.hOcc 521
  · exact hroot.hOcc 523
  · exact hroot.hOcc 524
  · exact hroot.hOcc 598
  · exact hroot.hOcc 604
  · exact hroot.hOcc 607
  · exact hroot.hOcc 609
  · exact hroot.hOcc 651
  · exact hroot.hOcc 656
  · exact hroot.hOcc 666
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (24 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (6 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (25 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25
  · change (∑ k, (if k = (1 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (35 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35

end QiushiMatmul
