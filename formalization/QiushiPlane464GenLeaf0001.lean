import QiushiPlane464GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane464GenLeaf0001Refs : Fin 51 → RowRef 202 50 := ![.occ 23, .occ 25, .occ 28, .occ 34, .occ 52, .occ 54, .occ 60, .occ 63, .occ 64, .occ 68, .occ 69, .occ 75, .occ 76, .occ 79, .occ 80, .occ 81, .occ 83, .occ 84, .occ 85, .occ 87, .occ 93, .occ 97, .occ 98, .occ 99, .occ 100, .occ 104, .occ 106, .occ 108, .occ 123, .occ 125, .occ 131, .occ 132, .occ 134, .occ 139, .occ 141, .occ 151, .occ 165, .occ 177, .occ 189, .occ 192, .occ 194, .occ 195, .occ 198, .sumGe, .nonneg 0, .nonneg 7, .nonneg 32, .branchLe 1 (0), .branchLe 15 (0), .branchGe 5 (1), .branchLe 37 (0)]

def plane464GenLeaf0001Mult : Fin 51 → Nat := ![17460, 1240804, 159302, 431510, 350008, 680546, 1397018, 216986, 617970, 1117196, 223218, 71601, 552045, 675591, 785911, 957704, 381810, 297422, 319042, 942162, 2232438, 581066, 710964, 913400, 878428, 1331654, 1080558, 691770, 54232, 37392, 485008, 366000, 394504, 173444, 915392, 384830, 12156, 617684, 292340, 12156, 959000, 136420, 1119246, 4149142, 4189424, 684072, 6742810, 3683358, 4149142, 2260108, 3233750]

theorem plane464GenLeaf0001 (x : Fin 50 → Int)
    (hroot : plane464GenOccSys.RootHolds x)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_37 : x 37 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane464GenLeaf0001Refs i).resolveCoeff plane464GenOccSys j)
    (fun i => (plane464GenLeaf0001Refs i).resolveRhs plane464GenOccSys) plane464GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane464GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 23
  · exact hroot.hOcc 25
  · exact hroot.hOcc 28
  · exact hroot.hOcc 34
  · exact hroot.hOcc 52
  · exact hroot.hOcc 54
  · exact hroot.hOcc 60
  · exact hroot.hOcc 63
  · exact hroot.hOcc 64
  · exact hroot.hOcc 68
  · exact hroot.hOcc 69
  · exact hroot.hOcc 75
  · exact hroot.hOcc 76
  · exact hroot.hOcc 79
  · exact hroot.hOcc 80
  · exact hroot.hOcc 81
  · exact hroot.hOcc 83
  · exact hroot.hOcc 84
  · exact hroot.hOcc 85
  · exact hroot.hOcc 87
  · exact hroot.hOcc 93
  · exact hroot.hOcc 97
  · exact hroot.hOcc 98
  · exact hroot.hOcc 99
  · exact hroot.hOcc 100
  · exact hroot.hOcc 104
  · exact hroot.hOcc 106
  · exact hroot.hOcc 108
  · exact hroot.hOcc 123
  · exact hroot.hOcc 125
  · exact hroot.hOcc 131
  · exact hroot.hOcc 132
  · exact hroot.hOcc 134
  · exact hroot.hOcc 139
  · exact hroot.hOcc 141
  · exact hroot.hOcc 151
  · exact hroot.hOcc 165
  · exact hroot.hOcc 177
  · exact hroot.hOcc 189
  · exact hroot.hOcc 192
  · exact hroot.hOcc 194
  · exact hroot.hOcc 195
  · exact hroot.hOcc 198
  · change (∑ j, (-1 : Int) * x j) ≤ -plane464GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (7 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (32 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (1 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (15 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (5 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5
  · change (∑ k, (if k = (37 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37

end QiushiMatmul
