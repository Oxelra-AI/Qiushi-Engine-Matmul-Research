import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0029Refs : Fin 50 → RowRef 726 49 := ![.occ 82, .occ 83, .occ 109, .occ 110, .occ 113, .occ 117, .occ 156, .occ 172, .occ 207, .occ 208, .occ 209, .occ 219, .occ 220, .occ 244, .occ 250, .occ 256, .occ 257, .occ 284, .occ 311, .occ 315, .occ 320, .occ 324, .occ 328, .occ 329, .occ 340, .occ 358, .occ 377, .occ 401, .occ 402, .occ 414, .occ 431, .occ 528, .occ 534, .occ 548, .occ 568, .occ 585, .occ 586, .occ 607, .occ 626, .occ 647, .occ 700, .occ 711, .occ 723, .sumGe, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchLe 29 (0), .branchGe 46 (1), .branchGe 14 (1)]

def plane491GenLeaf0029Mult : Fin 50 → Nat := ![315527, 205910, 15560, 34289, 190156, 116605, 34237, 30869, 140588, 36864, 228325, 140972, 12958, 43306, 69631, 30869, 56208, 18806, 47505, 64606, 114829, 28518, 157182, 62021, 20922, 224911, 193037, 54522, 64095, 39672, 90923, 10695, 89351, 109077, 12977, 104581, 95984, 67403, 37421, 24444, 135120, 69104, 80382, 536881, 216297, 536881, 486483, 261082, 1635999, 1045095]

theorem plane491GenLeaf0029 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_46 : (1 : Int) ≤ x 46)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0029Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0029Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0029Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0029Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 82
  · exact hroot.hOcc 83
  · exact hroot.hOcc 109
  · exact hroot.hOcc 110
  · exact hroot.hOcc 113
  · exact hroot.hOcc 117
  · exact hroot.hOcc 156
  · exact hroot.hOcc 172
  · exact hroot.hOcc 207
  · exact hroot.hOcc 208
  · exact hroot.hOcc 209
  · exact hroot.hOcc 219
  · exact hroot.hOcc 220
  · exact hroot.hOcc 244
  · exact hroot.hOcc 250
  · exact hroot.hOcc 256
  · exact hroot.hOcc 257
  · exact hroot.hOcc 284
  · exact hroot.hOcc 311
  · exact hroot.hOcc 315
  · exact hroot.hOcc 320
  · exact hroot.hOcc 324
  · exact hroot.hOcc 328
  · exact hroot.hOcc 329
  · exact hroot.hOcc 340
  · exact hroot.hOcc 358
  · exact hroot.hOcc 377
  · exact hroot.hOcc 401
  · exact hroot.hOcc 402
  · exact hroot.hOcc 414
  · exact hroot.hOcc 431
  · exact hroot.hOcc 528
  · exact hroot.hOcc 534
  · exact hroot.hOcc 548
  · exact hroot.hOcc 568
  · exact hroot.hOcc 585
  · exact hroot.hOcc 586
  · exact hroot.hOcc 607
  · exact hroot.hOcc 626
  · exact hroot.hOcc 647
  · exact hroot.hOcc 700
  · exact hroot.hOcc 711
  · exact hroot.hOcc 723
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (46 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_46
  · change (∑ k, (if k = (14 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14

end QiushiMatmul
