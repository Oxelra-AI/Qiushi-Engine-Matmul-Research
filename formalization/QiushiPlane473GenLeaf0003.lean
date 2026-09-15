import QiushiPlane473GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane473GenLeaf0003Refs : Fin 60 → RowRef 153 59 := ![.occ 5, .occ 6, .occ 14, .occ 17, .occ 18, .occ 22, .occ 24, .occ 36, .occ 37, .occ 38, .occ 42, .occ 45, .occ 54, .occ 58, .occ 59, .occ 60, .occ 61, .occ 62, .occ 64, .occ 65, .occ 68, .occ 71, .occ 72, .occ 77, .occ 79, .occ 80, .occ 83, .occ 90, .occ 93, .occ 94, .occ 98, .occ 99, .occ 104, .occ 112, .occ 114, .occ 121, .occ 124, .occ 128, .occ 131, .occ 135, .occ 141, .occ 142, .occ 143, .occ 146, .occ 150, .sumGe, .nonneg 3, .nonneg 16, .nonneg 19, .nonneg 30, .nonneg 36, .nonneg 38, .nonneg 43, .nonneg 46, .nonneg 50, .nonneg 51, .nonneg 56, .nonneg 58, .branchLe 40 (0), .branchGe 14 (1)]

def plane473GenLeaf0003Mult : Fin 60 → Nat := ![6642, 45042, 339473, 902796, 506011, 1751064, 753020, 552995, 953317, 880074, 326760, 527835, 249744, 426459, 114346, 1012757, 658143, 664963, 290283, 24940, 727003, 187954, 98454, 1082008, 217204, 183834, 46491, 957946, 169058, 58915, 162393, 229703, 420828, 80132, 132818, 23126, 118338, 156826, 137098, 742769, 71072, 95661, 340413, 139253, 196673, 2043398, 342988, 1424627, 559533, 330875, 1291093, 287805, 770088, 1537836, 1315771, 1264432, 185031, 659089, 1061161, 7825632]

theorem plane473GenLeaf0003 (x : Fin 59 → Int)
    (hroot : plane473GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hUB_40 : x 40 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane473GenLeaf0003Refs i).resolveCoeff plane473GenOccSys j)
    (fun i => (plane473GenLeaf0003Refs i).resolveRhs plane473GenOccSys) plane473GenLeaf0003Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane473GenLeaf0003Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · exact hroot.hOcc 6
  · exact hroot.hOcc 14
  · exact hroot.hOcc 17
  · exact hroot.hOcc 18
  · exact hroot.hOcc 22
  · exact hroot.hOcc 24
  · exact hroot.hOcc 36
  · exact hroot.hOcc 37
  · exact hroot.hOcc 38
  · exact hroot.hOcc 42
  · exact hroot.hOcc 45
  · exact hroot.hOcc 54
  · exact hroot.hOcc 58
  · exact hroot.hOcc 59
  · exact hroot.hOcc 60
  · exact hroot.hOcc 61
  · exact hroot.hOcc 62
  · exact hroot.hOcc 64
  · exact hroot.hOcc 65
  · exact hroot.hOcc 68
  · exact hroot.hOcc 71
  · exact hroot.hOcc 72
  · exact hroot.hOcc 77
  · exact hroot.hOcc 79
  · exact hroot.hOcc 80
  · exact hroot.hOcc 83
  · exact hroot.hOcc 90
  · exact hroot.hOcc 93
  · exact hroot.hOcc 94
  · exact hroot.hOcc 98
  · exact hroot.hOcc 99
  · exact hroot.hOcc 104
  · exact hroot.hOcc 112
  · exact hroot.hOcc 114
  · exact hroot.hOcc 121
  · exact hroot.hOcc 124
  · exact hroot.hOcc 128
  · exact hroot.hOcc 131
  · exact hroot.hOcc 135
  · exact hroot.hOcc 141
  · exact hroot.hOcc 142
  · exact hroot.hOcc 143
  · exact hroot.hOcc 146
  · exact hroot.hOcc 150
  · change (∑ j, (-1 : Int) * x j) ≤ -plane473GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (16 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (19 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (30 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (36 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (38 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (43 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 43
  · change (∑ k, (if k = (46 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (50 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (51 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 51
  · change (∑ k, (if k = (56 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 56
  · change (∑ k, (if k = (58 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 58
  · change (∑ k, (if k = (40 : Fin 59) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (14 : Fin 59) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14

end QiushiMatmul
