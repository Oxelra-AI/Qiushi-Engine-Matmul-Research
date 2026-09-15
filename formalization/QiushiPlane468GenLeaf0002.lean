import QiushiPlane468GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane468GenLeaf0002Refs : Fin 63 → RowRef 253 62 := ![.occ 2, .occ 6, .occ 22, .occ 25, .occ 29, .occ 30, .occ 36, .occ 37, .occ 61, .occ 70, .occ 79, .occ 81, .occ 82, .occ 84, .occ 100, .occ 103, .occ 105, .occ 107, .occ 111, .occ 116, .occ 117, .occ 121, .occ 124, .occ 130, .occ 135, .occ 139, .occ 144, .occ 145, .occ 157, .occ 164, .occ 167, .occ 169, .occ 177, .occ 187, .occ 189, .occ 191, .occ 195, .occ 202, .occ 215, .occ 221, .occ 231, .occ 236, .occ 237, .occ 238, .occ 240, .occ 242, .occ 243, .occ 245, .occ 246, .occ 251, .sumGe, .nonneg 20, .nonneg 34, .nonneg 39, .nonneg 46, .nonneg 59, .nonneg 60, .branchLe 28 (0), .branchGe 51 (1), .branchLe 15 (0), .branchLe 2 (0), .branchLe 33 (0), .branchLe 4 (0)]

def plane468GenLeaf0002Mult : Fin 63 → Nat := ![88792156, 157121364, 36128728, 45360608, 110426820, 28695288, 69711060, 44481596, 48648860, 25739496, 35882376, 40979604, 34502452, 81908888, 18239472, 54876176, 6564140, 163822532, 21679672, 136028144, 11205480, 93602856, 182911504, 77028932, 94444832, 52462908, 1808728, 39846824, 36981280, 2695584, 67382098, 54371646, 18524062, 50793252, 12619966, 35400876, 85572748, 23341368, 24414164, 15390896, 31874166, 70618050, 44302979, 8411378, 44403318, 30747609, 72987107, 49214678, 10136807, 5439104, 420925608, 42202736, 346059864, 78417724, 59731600, 140206792, 4779452, 293398376, 350971632, 252536484, 420925608, 250152504, 274836428]

theorem plane468GenLeaf0002 (x : Fin 62 → Int)
    (hroot : plane468GenOccSys.RootHolds x)
    (hLB_51 : (1 : Int) ≤ x 51)
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane468GenLeaf0002Refs i).resolveCoeff plane468GenOccSys j)
    (fun i => (plane468GenLeaf0002Refs i).resolveRhs plane468GenOccSys) plane468GenLeaf0002Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane468GenLeaf0002Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · exact hroot.hOcc 6
  · exact hroot.hOcc 22
  · exact hroot.hOcc 25
  · exact hroot.hOcc 29
  · exact hroot.hOcc 30
  · exact hroot.hOcc 36
  · exact hroot.hOcc 37
  · exact hroot.hOcc 61
  · exact hroot.hOcc 70
  · exact hroot.hOcc 79
  · exact hroot.hOcc 81
  · exact hroot.hOcc 82
  · exact hroot.hOcc 84
  · exact hroot.hOcc 100
  · exact hroot.hOcc 103
  · exact hroot.hOcc 105
  · exact hroot.hOcc 107
  · exact hroot.hOcc 111
  · exact hroot.hOcc 116
  · exact hroot.hOcc 117
  · exact hroot.hOcc 121
  · exact hroot.hOcc 124
  · exact hroot.hOcc 130
  · exact hroot.hOcc 135
  · exact hroot.hOcc 139
  · exact hroot.hOcc 144
  · exact hroot.hOcc 145
  · exact hroot.hOcc 157
  · exact hroot.hOcc 164
  · exact hroot.hOcc 167
  · exact hroot.hOcc 169
  · exact hroot.hOcc 177
  · exact hroot.hOcc 187
  · exact hroot.hOcc 189
  · exact hroot.hOcc 191
  · exact hroot.hOcc 195
  · exact hroot.hOcc 202
  · exact hroot.hOcc 215
  · exact hroot.hOcc 221
  · exact hroot.hOcc 231
  · exact hroot.hOcc 236
  · exact hroot.hOcc 237
  · exact hroot.hOcc 238
  · exact hroot.hOcc 240
  · exact hroot.hOcc 242
  · exact hroot.hOcc 243
  · exact hroot.hOcc 245
  · exact hroot.hOcc 246
  · exact hroot.hOcc 251
  · change (∑ j, (-1 : Int) * x j) ≤ -plane468GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (20 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (34 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 34
  · change (∑ k, (if k = (39 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (46 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (59 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (60 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 60
  · change (∑ k, (if k = (28 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (51 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_51
  · change (∑ k, (if k = (15 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (33 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (4 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4

end QiushiMatmul
