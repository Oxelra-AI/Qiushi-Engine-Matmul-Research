import QiushiPlane455GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane455GenLeaf0002Refs : Fin 49 → RowRef 124 48 := ![.occ 15, .occ 16, .occ 18, .occ 19, .occ 23, .occ 24, .occ 25, .occ 28, .occ 36, .occ 41, .occ 44, .occ 45, .occ 46, .occ 48, .occ 49, .occ 52, .occ 56, .occ 57, .occ 61, .occ 63, .occ 64, .occ 67, .occ 70, .occ 71, .occ 77, .occ 78, .occ 80, .occ 81, .occ 82, .occ 89, .occ 92, .occ 95, .occ 96, .occ 98, .occ 99, .occ 104, .occ 107, .occ 108, .occ 111, .occ 113, .occ 114, .occ 117, .occ 119, .sumGe, .nonneg 22, .nonneg 29, .nonneg 44, .branchGe 14 (1), .branchLe 8 (0)]

def plane455GenLeaf0002Mult : Fin 49 → Nat := ![123716, 15683, 160992, 190642, 96714, 169901, 141425, 117311, 123132, 299453, 14024, 315160, 42529, 60048, 198464, 102243, 194801, 73562, 342820, 220536, 120214, 124780, 119558, 186487, 161907, 41840, 9984, 52385, 101114, 159700, 26362, 31963, 110114, 55373, 2253, 200465, 59432, 135677, 78984, 86133, 107260, 46608, 13452, 701619, 224498, 227719, 98148, 1236523, 701619]

theorem plane455GenLeaf0002 (x : Fin 48 → Int)
    (hroot : plane455GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hUB_8 : x 8 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane455GenLeaf0002Refs i).resolveCoeff plane455GenOccSys j)
    (fun i => (plane455GenLeaf0002Refs i).resolveRhs plane455GenOccSys) plane455GenLeaf0002Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane455GenLeaf0002Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 15
  · exact hroot.hOcc 16
  · exact hroot.hOcc 18
  · exact hroot.hOcc 19
  · exact hroot.hOcc 23
  · exact hroot.hOcc 24
  · exact hroot.hOcc 25
  · exact hroot.hOcc 28
  · exact hroot.hOcc 36
  · exact hroot.hOcc 41
  · exact hroot.hOcc 44
  · exact hroot.hOcc 45
  · exact hroot.hOcc 46
  · exact hroot.hOcc 48
  · exact hroot.hOcc 49
  · exact hroot.hOcc 52
  · exact hroot.hOcc 56
  · exact hroot.hOcc 57
  · exact hroot.hOcc 61
  · exact hroot.hOcc 63
  · exact hroot.hOcc 64
  · exact hroot.hOcc 67
  · exact hroot.hOcc 70
  · exact hroot.hOcc 71
  · exact hroot.hOcc 77
  · exact hroot.hOcc 78
  · exact hroot.hOcc 80
  · exact hroot.hOcc 81
  · exact hroot.hOcc 82
  · exact hroot.hOcc 89
  · exact hroot.hOcc 92
  · exact hroot.hOcc 95
  · exact hroot.hOcc 96
  · exact hroot.hOcc 98
  · exact hroot.hOcc 99
  · exact hroot.hOcc 104
  · exact hroot.hOcc 107
  · exact hroot.hOcc 108
  · exact hroot.hOcc 111
  · exact hroot.hOcc 113
  · exact hroot.hOcc 114
  · exact hroot.hOcc 117
  · exact hroot.hOcc 119
  · change (∑ j, (-1 : Int) * x j) ≤ -plane455GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (22 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (29 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (44 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (14 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (8 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8

end QiushiMatmul
