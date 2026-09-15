import QiushiPlane476GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane476GenLeaf0001Refs : Fin 51 → RowRef 113 50 := ![.occ 13, .occ 14, .occ 15, .occ 17, .occ 20, .occ 22, .occ 26, .occ 27, .occ 28, .occ 29, .occ 32, .occ 35, .occ 36, .occ 37, .occ 42, .occ 43, .occ 44, .occ 50, .occ 51, .occ 54, .occ 55, .occ 56, .occ 57, .occ 61, .occ 63, .occ 67, .occ 69, .occ 70, .occ 75, .occ 79, .occ 81, .occ 88, .occ 89, .occ 90, .occ 93, .occ 95, .occ 96, .occ 102, .occ 103, .occ 105, .occ 106, .occ 107, .occ 108, .occ 109, .sumGe, .nonneg 0, .nonneg 16, .nonneg 27, .nonneg 30, .branchLe 35 (0), .branchGe 11 (1)]

def plane476GenLeaf0001Mult : Fin 51 → Nat := ![28546, 39953, 64253, 61865, 76812, 87436, 3758, 53394, 36359, 55821, 71661, 30943, 48758, 4301, 55039, 47941, 60441, 14975, 17650, 107597, 12540, 73124, 31074, 8240, 60300, 22037, 17023, 26164, 12596, 19998, 14272, 1526, 20739, 13820, 9550, 26882, 28734, 13664, 11189, 12746, 9589, 15451, 21840, 9598, 149860, 57718, 32802, 21765, 66618, 88588, 466306]

theorem plane476GenLeaf0001 (x : Fin 50 → Int)
    (hroot : plane476GenOccSys.RootHolds x)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane476GenLeaf0001Refs i).resolveCoeff plane476GenOccSys j)
    (fun i => (plane476GenLeaf0001Refs i).resolveRhs plane476GenOccSys) plane476GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane476GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 13
  · exact hroot.hOcc 14
  · exact hroot.hOcc 15
  · exact hroot.hOcc 17
  · exact hroot.hOcc 20
  · exact hroot.hOcc 22
  · exact hroot.hOcc 26
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · exact hroot.hOcc 29
  · exact hroot.hOcc 32
  · exact hroot.hOcc 35
  · exact hroot.hOcc 36
  · exact hroot.hOcc 37
  · exact hroot.hOcc 42
  · exact hroot.hOcc 43
  · exact hroot.hOcc 44
  · exact hroot.hOcc 50
  · exact hroot.hOcc 51
  · exact hroot.hOcc 54
  · exact hroot.hOcc 55
  · exact hroot.hOcc 56
  · exact hroot.hOcc 57
  · exact hroot.hOcc 61
  · exact hroot.hOcc 63
  · exact hroot.hOcc 67
  · exact hroot.hOcc 69
  · exact hroot.hOcc 70
  · exact hroot.hOcc 75
  · exact hroot.hOcc 79
  · exact hroot.hOcc 81
  · exact hroot.hOcc 88
  · exact hroot.hOcc 89
  · exact hroot.hOcc 90
  · exact hroot.hOcc 93
  · exact hroot.hOcc 95
  · exact hroot.hOcc 96
  · exact hroot.hOcc 102
  · exact hroot.hOcc 103
  · exact hroot.hOcc 105
  · exact hroot.hOcc 106
  · exact hroot.hOcc 107
  · exact hroot.hOcc 108
  · exact hroot.hOcc 109
  · change (∑ j, (-1 : Int) * x j) ≤ -plane476GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (16 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (27 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27
  · change (∑ k, (if k = (30 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (35 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (11 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11

end QiushiMatmul
