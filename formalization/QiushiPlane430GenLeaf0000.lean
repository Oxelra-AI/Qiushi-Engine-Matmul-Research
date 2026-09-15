import QiushiPlane430GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane430GenLeaf0000Refs : Fin 36 → RowRef 57 36 := ![.occ 24, .occ 25, .occ 26, .occ 27, .occ 28, .occ 29, .occ 30, .occ 31, .occ 32, .occ 33, .occ 34, .occ 35, .occ 36, .occ 37, .occ 38, .occ 39, .occ 40, .occ 41, .occ 42, .occ 43, .occ 44, .occ 45, .occ 46, .occ 47, .occ 48, .occ 49, .occ 50, .occ 51, .occ 52, .occ 53, .occ 54, .occ 55, .occ 56, .sumGe, .nonneg 4, .nonneg 27]

def plane430GenLeaf0000Mult : Fin 36 → Nat := ![404, 502, 504, 856, 502, 916, 884, 1298, 54, 446, 178, 520, 268, 150, 162, 530, 335, 515, 340, 52, 298, 398, 376, 459, 186, 437, 514, 586, 162, 138, 477, 563, 74, 2302, 280, 138]

theorem plane430GenLeaf0000 (x : Fin 36 → Int)
    (hroot : plane430GenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane430GenLeaf0000Refs i).resolveCoeff plane430GenOccSys j)
    (fun i => (plane430GenLeaf0000Refs i).resolveRhs plane430GenOccSys) plane430GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane430GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 24
  · exact hroot.hOcc 25
  · exact hroot.hOcc 26
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · exact hroot.hOcc 29
  · exact hroot.hOcc 30
  · exact hroot.hOcc 31
  · exact hroot.hOcc 32
  · exact hroot.hOcc 33
  · exact hroot.hOcc 34
  · exact hroot.hOcc 35
  · exact hroot.hOcc 36
  · exact hroot.hOcc 37
  · exact hroot.hOcc 38
  · exact hroot.hOcc 39
  · exact hroot.hOcc 40
  · exact hroot.hOcc 41
  · exact hroot.hOcc 42
  · exact hroot.hOcc 43
  · exact hroot.hOcc 44
  · exact hroot.hOcc 45
  · exact hroot.hOcc 46
  · exact hroot.hOcc 47
  · exact hroot.hOcc 48
  · exact hroot.hOcc 49
  · exact hroot.hOcc 50
  · exact hroot.hOcc 51
  · exact hroot.hOcc 52
  · exact hroot.hOcc 53
  · exact hroot.hOcc 54
  · exact hroot.hOcc 55
  · exact hroot.hOcc 56
  · change (∑ j, (-1 : Int) * x j) ≤ -plane430GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (4 : Fin 36) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (27 : Fin 36) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27

end QiushiMatmul
