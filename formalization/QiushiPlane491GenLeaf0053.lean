import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0053Refs : Fin 50 → RowRef 726 49 := ![.occ 100, .occ 114, .occ 120, .occ 150, .occ 190, .occ 193, .occ 194, .occ 231, .occ 254, .occ 293, .occ 299, .occ 305, .occ 320, .occ 325, .occ 382, .occ 383, .occ 392, .occ 401, .occ 409, .occ 416, .occ 424, .occ 446, .occ 548, .occ 571, .occ 580, .occ 581, .occ 585, .occ 631, .occ 632, .occ 640, .occ 642, .occ 644, .occ 653, .occ 665, .occ 691, .occ 714, .occ 715, .sumGe, .nonneg 5, .nonneg 24, .nonneg 37, .branchLe 31 (0), .branchLe 16 (0), .branchGe 27 (1), .branchLe 11 (0), .branchLe 23 (0), .branchLe 0 (0), .branchGe 43 (1), .branchLe 48 (0), .branchGe 15 (1)]

def plane491GenLeaf0053Mult : Fin 50 → Nat := ![94557, 183670, 51469, 24992, 43419, 45411, 208, 4635, 58086, 2546, 43624, 8832, 62234, 11411, 11805, 19123, 48826, 11040, 48158, 31920, 57192, 567, 89102, 15675, 25616, 24699, 37230, 33715, 11805, 10602, 31920, 94662, 62081, 41872, 22845, 29677, 30811, 226286, 27278, 51966, 9113, 84710, 200670, 421750, 183670, 158245, 203441, 578338, 116933, 370326]

theorem plane491GenLeaf0053 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_43 : (1 : Int) ≤ x 43)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_48 : x 48 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0053Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0053Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0053Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0053Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 100
  · exact hroot.hOcc 114
  · exact hroot.hOcc 120
  · exact hroot.hOcc 150
  · exact hroot.hOcc 190
  · exact hroot.hOcc 193
  · exact hroot.hOcc 194
  · exact hroot.hOcc 231
  · exact hroot.hOcc 254
  · exact hroot.hOcc 293
  · exact hroot.hOcc 299
  · exact hroot.hOcc 305
  · exact hroot.hOcc 320
  · exact hroot.hOcc 325
  · exact hroot.hOcc 382
  · exact hroot.hOcc 383
  · exact hroot.hOcc 392
  · exact hroot.hOcc 401
  · exact hroot.hOcc 409
  · exact hroot.hOcc 416
  · exact hroot.hOcc 424
  · exact hroot.hOcc 446
  · exact hroot.hOcc 548
  · exact hroot.hOcc 571
  · exact hroot.hOcc 580
  · exact hroot.hOcc 581
  · exact hroot.hOcc 585
  · exact hroot.hOcc 631
  · exact hroot.hOcc 632
  · exact hroot.hOcc 640
  · exact hroot.hOcc 642
  · exact hroot.hOcc 644
  · exact hroot.hOcc 653
  · exact hroot.hOcc 665
  · exact hroot.hOcc 691
  · exact hroot.hOcc 714
  · exact hroot.hOcc 715
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (5 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (24 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (37 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (11 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (23 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (0 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (43 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_43
  · change (∑ k, (if k = (48 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_48
  · change (∑ k, (if k = (15 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15

end QiushiMatmul
