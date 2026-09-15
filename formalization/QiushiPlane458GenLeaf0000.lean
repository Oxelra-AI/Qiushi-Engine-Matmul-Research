import QiushiPlane458GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane458GenLeaf0000Refs : Fin 57 → RowRef 203 56 := ![.occ 7, .occ 8, .occ 15, .occ 16, .occ 17, .occ 18, .occ 33, .occ 35, .occ 37, .occ 46, .occ 47, .occ 49, .occ 53, .occ 54, .occ 56, .occ 62, .occ 64, .occ 65, .occ 74, .occ 75, .occ 84, .occ 98, .occ 99, .occ 101, .occ 106, .occ 107, .occ 109, .occ 110, .occ 111, .occ 114, .occ 120, .occ 122, .occ 127, .occ 129, .occ 134, .occ 138, .occ 145, .occ 151, .occ 158, .occ 172, .occ 175, .occ 185, .occ 190, .occ 191, .occ 194, .occ 197, .occ 200, .occ 202, .sumGe, .nonneg 13, .nonneg 32, .nonneg 43, .nonneg 52, .branchLe 46 (0), .branchLe 30 (0), .branchLe 31 (0), .branchLe 9 (0)]

def plane458GenLeaf0000Mult : Fin 57 → Nat := ![76884, 15858, 870938, 198020, 659806, 91452, 297374, 232486, 196142, 1157646, 43992, 986126, 57092, 542330, 211310, 1108772, 88520, 988300, 68782, 1258044, 789470, 289526, 480608, 99978, 1247994, 52046, 85092, 81504, 1155730, 452800, 120832, 183705, 213159, 61963, 117279, 36951, 455479, 127952, 28717, 3895, 70670, 335331, 27884, 78716, 346951, 285850, 62080, 321506, 2065348, 287624, 779940, 335328, 1156564, 2065348, 2065348, 1530798, 1996566]

theorem plane458GenLeaf0000 (x : Fin 56 → Int)
    (hroot : plane458GenOccSys.RootHolds x)
    (hUB_46 : x 46 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane458GenLeaf0000Refs i).resolveCoeff plane458GenOccSys j)
    (fun i => (plane458GenLeaf0000Refs i).resolveRhs plane458GenOccSys) plane458GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane458GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 7
  · exact hroot.hOcc 8
  · exact hroot.hOcc 15
  · exact hroot.hOcc 16
  · exact hroot.hOcc 17
  · exact hroot.hOcc 18
  · exact hroot.hOcc 33
  · exact hroot.hOcc 35
  · exact hroot.hOcc 37
  · exact hroot.hOcc 46
  · exact hroot.hOcc 47
  · exact hroot.hOcc 49
  · exact hroot.hOcc 53
  · exact hroot.hOcc 54
  · exact hroot.hOcc 56
  · exact hroot.hOcc 62
  · exact hroot.hOcc 64
  · exact hroot.hOcc 65
  · exact hroot.hOcc 74
  · exact hroot.hOcc 75
  · exact hroot.hOcc 84
  · exact hroot.hOcc 98
  · exact hroot.hOcc 99
  · exact hroot.hOcc 101
  · exact hroot.hOcc 106
  · exact hroot.hOcc 107
  · exact hroot.hOcc 109
  · exact hroot.hOcc 110
  · exact hroot.hOcc 111
  · exact hroot.hOcc 114
  · exact hroot.hOcc 120
  · exact hroot.hOcc 122
  · exact hroot.hOcc 127
  · exact hroot.hOcc 129
  · exact hroot.hOcc 134
  · exact hroot.hOcc 138
  · exact hroot.hOcc 145
  · exact hroot.hOcc 151
  · exact hroot.hOcc 158
  · exact hroot.hOcc 172
  · exact hroot.hOcc 175
  · exact hroot.hOcc 185
  · exact hroot.hOcc 190
  · exact hroot.hOcc 191
  · exact hroot.hOcc 194
  · exact hroot.hOcc 197
  · exact hroot.hOcc 200
  · exact hroot.hOcc 202
  · change (∑ j, (-1 : Int) * x j) ≤ -plane458GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (13 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (32 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (43 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 43
  · change (∑ k, (if k = (52 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (46 : Fin 56) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_46
  · change (∑ k, (if k = (30 : Fin 56) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (31 : Fin 56) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (9 : Fin 56) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9

end QiushiMatmul
