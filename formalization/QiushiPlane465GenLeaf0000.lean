import QiushiPlane465GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane465GenLeaf0000Refs : Fin 58 → RowRef 88 57 := ![.occ 6, .occ 7, .occ 9, .occ 10, .occ 18, .occ 19, .occ 23, .occ 24, .occ 26, .occ 28, .occ 36, .occ 37, .occ 38, .occ 39, .occ 40, .occ 41, .occ 42, .occ 43, .occ 46, .occ 47, .occ 49, .occ 51, .occ 52, .occ 54, .occ 56, .occ 57, .occ 58, .occ 59, .occ 60, .occ 61, .occ 62, .occ 63, .occ 64, .occ 65, .occ 67, .occ 68, .occ 69, .occ 70, .occ 74, .occ 75, .occ 76, .occ 77, .occ 79, .occ 80, .occ 82, .occ 83, .occ 84, .occ 85, .occ 86, .occ 87, .sumGe, .nonneg 0, .nonneg 16, .nonneg 19, .nonneg 36, .nonneg 37, .nonneg 51, .branchLe 44 (0)]

def plane465GenLeaf0000Mult : Fin 58 → Nat := ![3860, 2900, 8292, 3548, 3774, 3666, 9384, 11837, 15106, 9119, 3472, 5306, 1798, 8024, 6436, 2926, 8350, 4050, 1514, 3818, 10220, 4886, 5955, 8008, 1376, 14505, 1370, 1017, 5735, 7719, 4165, 465, 4298, 2511, 2331, 1296, 279, 124, 2201, 541, 1505, 3407, 2201, 4002, 4836, 4765, 5745, 1819, 6665, 3388, 40765, 46996, 5694, 31848, 21214, 28168, 24738, 22878]

theorem plane465GenLeaf0000 (x : Fin 57 → Int)
    (hroot : plane465GenOccSys.RootHolds x)
    (hUB_44 : x 44 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane465GenLeaf0000Refs i).resolveCoeff plane465GenOccSys j)
    (fun i => (plane465GenLeaf0000Refs i).resolveRhs plane465GenOccSys) plane465GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane465GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 6
  · exact hroot.hOcc 7
  · exact hroot.hOcc 9
  · exact hroot.hOcc 10
  · exact hroot.hOcc 18
  · exact hroot.hOcc 19
  · exact hroot.hOcc 23
  · exact hroot.hOcc 24
  · exact hroot.hOcc 26
  · exact hroot.hOcc 28
  · exact hroot.hOcc 36
  · exact hroot.hOcc 37
  · exact hroot.hOcc 38
  · exact hroot.hOcc 39
  · exact hroot.hOcc 40
  · exact hroot.hOcc 41
  · exact hroot.hOcc 42
  · exact hroot.hOcc 43
  · exact hroot.hOcc 46
  · exact hroot.hOcc 47
  · exact hroot.hOcc 49
  · exact hroot.hOcc 51
  · exact hroot.hOcc 52
  · exact hroot.hOcc 54
  · exact hroot.hOcc 56
  · exact hroot.hOcc 57
  · exact hroot.hOcc 58
  · exact hroot.hOcc 59
  · exact hroot.hOcc 60
  · exact hroot.hOcc 61
  · exact hroot.hOcc 62
  · exact hroot.hOcc 63
  · exact hroot.hOcc 64
  · exact hroot.hOcc 65
  · exact hroot.hOcc 67
  · exact hroot.hOcc 68
  · exact hroot.hOcc 69
  · exact hroot.hOcc 70
  · exact hroot.hOcc 74
  · exact hroot.hOcc 75
  · exact hroot.hOcc 76
  · exact hroot.hOcc 77
  · exact hroot.hOcc 79
  · exact hroot.hOcc 80
  · exact hroot.hOcc 82
  · exact hroot.hOcc 83
  · exact hroot.hOcc 84
  · exact hroot.hOcc 85
  · exact hroot.hOcc 86
  · exact hroot.hOcc 87
  · change (∑ j, (-1 : Int) * x j) ≤ -plane465GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 57) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (16 : Fin 57) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (19 : Fin 57) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (36 : Fin 57) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (37 : Fin 57) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (51 : Fin 57) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 51
  · change (∑ k, (if k = (44 : Fin 57) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44

end QiushiMatmul
