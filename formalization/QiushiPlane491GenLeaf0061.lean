import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0061Refs : Fin 50 → RowRef 726 49 := ![.occ 79, .occ 97, .occ 100, .occ 103, .occ 106, .occ 111, .occ 119, .occ 128, .occ 132, .occ 160, .occ 187, .occ 232, .occ 237, .occ 260, .occ 280, .occ 300, .occ 326, .occ 341, .occ 343, .occ 368, .occ 389, .occ 422, .occ 424, .occ 489, .occ 490, .occ 508, .occ 541, .occ 573, .occ 603, .occ 606, .occ 628, .occ 632, .occ 642, .occ 644, .occ 647, .occ 648, .occ 686, .occ 692, .occ 715, .sumGe, .nonneg 13, .branchLe 31 (0), .branchLe 16 (0), .branchGe 27 (1), .branchGe 11 (1), .branchLe 44 (0), .branchLe 46 (0), .branchLe 18 (0), .branchGe 25 (1), .branchGe 0 (1)]

def plane491GenLeaf0061Mult : Fin 50 → Nat := ![10242, 2214, 4076, 6325, 4543, 3425, 4130, 478, 4989, 355, 3022, 7103, 607, 3455, 464, 2376, 456, 1398, 6978, 2388, 1607, 843, 2089, 6392, 1393, 258, 820, 2611, 1245, 744, 2951, 1233, 1117, 4450, 1507, 1567, 1672, 1598, 531, 12779, 5844, 10468, 10566, 32570, 24883, 12779, 7677, 12779, 13790, 31570]

theorem plane491GenLeaf0061 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_46 : x 46 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0061Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0061Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0061Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0061Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 79
  · exact hroot.hOcc 97
  · exact hroot.hOcc 100
  · exact hroot.hOcc 103
  · exact hroot.hOcc 106
  · exact hroot.hOcc 111
  · exact hroot.hOcc 119
  · exact hroot.hOcc 128
  · exact hroot.hOcc 132
  · exact hroot.hOcc 160
  · exact hroot.hOcc 187
  · exact hroot.hOcc 232
  · exact hroot.hOcc 237
  · exact hroot.hOcc 260
  · exact hroot.hOcc 280
  · exact hroot.hOcc 300
  · exact hroot.hOcc 326
  · exact hroot.hOcc 341
  · exact hroot.hOcc 343
  · exact hroot.hOcc 368
  · exact hroot.hOcc 389
  · exact hroot.hOcc 422
  · exact hroot.hOcc 424
  · exact hroot.hOcc 489
  · exact hroot.hOcc 490
  · exact hroot.hOcc 508
  · exact hroot.hOcc 541
  · exact hroot.hOcc 573
  · exact hroot.hOcc 603
  · exact hroot.hOcc 606
  · exact hroot.hOcc 628
  · exact hroot.hOcc 632
  · exact hroot.hOcc 642
  · exact hroot.hOcc 644
  · exact hroot.hOcc 647
  · exact hroot.hOcc 648
  · exact hroot.hOcc 686
  · exact hroot.hOcc 692
  · exact hroot.hOcc 715
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (13 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (11 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11
  · change (∑ k, (if k = (44 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (46 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_46
  · change (∑ k, (if k = (18 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (25 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25
  · change (∑ k, (if k = (0 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
