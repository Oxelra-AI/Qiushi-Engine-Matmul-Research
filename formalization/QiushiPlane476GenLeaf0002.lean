import QiushiPlane476GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane476GenLeaf0002Refs : Fin 51 → RowRef 113 50 := ![.occ 16, .occ 20, .occ 23, .occ 25, .occ 29, .occ 30, .occ 31, .occ 33, .occ 34, .occ 35, .occ 37, .occ 39, .occ 40, .occ 41, .occ 43, .occ 44, .occ 45, .occ 46, .occ 51, .occ 53, .occ 54, .occ 55, .occ 56, .occ 57, .occ 58, .occ 59, .occ 61, .occ 64, .occ 65, .occ 66, .occ 68, .occ 71, .occ 74, .occ 76, .occ 77, .occ 79, .occ 82, .occ 83, .occ 86, .occ 90, .occ 91, .occ 92, .occ 94, .occ 99, .occ 100, .occ 104, .occ 111, .sumGe, .nonneg 9, .nonneg 26, .branchGe 35 (1)]

def plane476GenLeaf0002Mult : Fin 51 → Nat := ![208961, 481804, 621005, 452068, 393211, 109002, 1146177, 37207, 251471, 145463, 287941, 36407, 530509, 194720, 498030, 85286, 457147, 1402231, 87964, 546052, 457147, 2458676, 183293, 542254, 228903, 217459, 157291, 171858, 317608, 290140, 1331711, 27832, 259981, 66118, 668367, 1206246, 44224, 617407, 289234, 130650, 1100113, 7206, 549916, 282273, 637244, 510620, 254313, 2915823, 718830, 506249, 10165647]

theorem plane476GenLeaf0002 (x : Fin 50 → Int)
    (hroot : plane476GenOccSys.RootHolds x)
    (hLB_35 : (1 : Int) ≤ x 35)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane476GenLeaf0002Refs i).resolveCoeff plane476GenOccSys j)
    (fun i => (plane476GenLeaf0002Refs i).resolveRhs plane476GenOccSys) plane476GenLeaf0002Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane476GenLeaf0002Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 16
  · exact hroot.hOcc 20
  · exact hroot.hOcc 23
  · exact hroot.hOcc 25
  · exact hroot.hOcc 29
  · exact hroot.hOcc 30
  · exact hroot.hOcc 31
  · exact hroot.hOcc 33
  · exact hroot.hOcc 34
  · exact hroot.hOcc 35
  · exact hroot.hOcc 37
  · exact hroot.hOcc 39
  · exact hroot.hOcc 40
  · exact hroot.hOcc 41
  · exact hroot.hOcc 43
  · exact hroot.hOcc 44
  · exact hroot.hOcc 45
  · exact hroot.hOcc 46
  · exact hroot.hOcc 51
  · exact hroot.hOcc 53
  · exact hroot.hOcc 54
  · exact hroot.hOcc 55
  · exact hroot.hOcc 56
  · exact hroot.hOcc 57
  · exact hroot.hOcc 58
  · exact hroot.hOcc 59
  · exact hroot.hOcc 61
  · exact hroot.hOcc 64
  · exact hroot.hOcc 65
  · exact hroot.hOcc 66
  · exact hroot.hOcc 68
  · exact hroot.hOcc 71
  · exact hroot.hOcc 74
  · exact hroot.hOcc 76
  · exact hroot.hOcc 77
  · exact hroot.hOcc 79
  · exact hroot.hOcc 82
  · exact hroot.hOcc 83
  · exact hroot.hOcc 86
  · exact hroot.hOcc 90
  · exact hroot.hOcc 91
  · exact hroot.hOcc 92
  · exact hroot.hOcc 94
  · exact hroot.hOcc 99
  · exact hroot.hOcc 100
  · exact hroot.hOcc 104
  · exact hroot.hOcc 111
  · change (∑ j, (-1 : Int) * x j) ≤ -plane476GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (9 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 9
  · change (∑ k, (if k = (26 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (35 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35

end QiushiMatmul
