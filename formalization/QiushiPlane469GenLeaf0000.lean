import QiushiPlane469GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane469GenLeaf0000Refs : Fin 61 → RowRef 217 60 := ![.occ 6, .occ 9, .occ 19, .occ 24, .occ 27, .occ 40, .occ 43, .occ 50, .occ 51, .occ 57, .occ 58, .occ 69, .occ 74, .occ 76, .occ 81, .occ 83, .occ 84, .occ 95, .occ 99, .occ 101, .occ 102, .occ 106, .occ 110, .occ 113, .occ 117, .occ 122, .occ 124, .occ 126, .occ 134, .occ 139, .occ 143, .occ 151, .occ 153, .occ 154, .occ 168, .occ 172, .occ 180, .occ 190, .occ 193, .occ 196, .occ 199, .occ 201, .occ 202, .occ 207, .occ 208, .occ 209, .occ 210, .occ 216, .sumGe, .nonneg 3, .nonneg 10, .nonneg 17, .nonneg 32, .nonneg 46, .branchLe 34 (0), .branchLe 13 (0), .branchLe 8 (0), .branchLe 54 (0), .branchLe 40 (0), .branchLe 45 (0), .branchLe 5 (0)]

def plane469GenLeaf0000Mult : Fin 61 → Nat := ![43493524, 114397714, 71114228, 82332314, 170593690, 95614074, 99338576, 25820442, 122862554, 384752602, 238250266, 342120746, 191961850, 78038166, 175488144, 247361456, 46153878, 344743438, 25574336, 200576504, 62516640, 64438514, 77911726, 142498114, 15153510, 191359856, 85623123, 49927018, 128870833, 163988178, 29610262, 211266062, 56926680, 47110429, 84193268, 7890426, 47609073, 45881151, 74720547, 28792311, 97287782, 33499755, 16556839, 201113714, 104065186, 80518661, 94941406, 1319541, 954924823, 717412364, 29831416, 408608432, 701329814, 75448564, 881441304, 710037080, 388980294, 660089948, 843426578, 515075412, 822067326]

theorem plane469GenLeaf0000 (x : Fin 60 → Int)
    (hroot : plane469GenOccSys.RootHolds x)
    (hUB_34 : x 34 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_54 : x 54 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    (hUB_45 : x 45 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane469GenLeaf0000Refs i).resolveCoeff plane469GenOccSys j)
    (fun i => (plane469GenLeaf0000Refs i).resolveRhs plane469GenOccSys) plane469GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane469GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 6
  · exact hroot.hOcc 9
  · exact hroot.hOcc 19
  · exact hroot.hOcc 24
  · exact hroot.hOcc 27
  · exact hroot.hOcc 40
  · exact hroot.hOcc 43
  · exact hroot.hOcc 50
  · exact hroot.hOcc 51
  · exact hroot.hOcc 57
  · exact hroot.hOcc 58
  · exact hroot.hOcc 69
  · exact hroot.hOcc 74
  · exact hroot.hOcc 76
  · exact hroot.hOcc 81
  · exact hroot.hOcc 83
  · exact hroot.hOcc 84
  · exact hroot.hOcc 95
  · exact hroot.hOcc 99
  · exact hroot.hOcc 101
  · exact hroot.hOcc 102
  · exact hroot.hOcc 106
  · exact hroot.hOcc 110
  · exact hroot.hOcc 113
  · exact hroot.hOcc 117
  · exact hroot.hOcc 122
  · exact hroot.hOcc 124
  · exact hroot.hOcc 126
  · exact hroot.hOcc 134
  · exact hroot.hOcc 139
  · exact hroot.hOcc 143
  · exact hroot.hOcc 151
  · exact hroot.hOcc 153
  · exact hroot.hOcc 154
  · exact hroot.hOcc 168
  · exact hroot.hOcc 172
  · exact hroot.hOcc 180
  · exact hroot.hOcc 190
  · exact hroot.hOcc 193
  · exact hroot.hOcc 196
  · exact hroot.hOcc 199
  · exact hroot.hOcc 201
  · exact hroot.hOcc 202
  · exact hroot.hOcc 207
  · exact hroot.hOcc 208
  · exact hroot.hOcc 209
  · exact hroot.hOcc 210
  · exact hroot.hOcc 216
  · change (∑ j, (-1 : Int) * x j) ≤ -plane469GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (10 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (17 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (32 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (46 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (34 : Fin 60) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (13 : Fin 60) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (8 : Fin 60) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (54 : Fin 60) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_54
  · change (∑ k, (if k = (40 : Fin 60) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (45 : Fin 60) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_45
  · change (∑ k, (if k = (5 : Fin 60) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5

end QiushiMatmul
