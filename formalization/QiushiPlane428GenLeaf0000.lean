import QiushiPlane428GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane428GenLeaf0000Refs : Fin 34 → RowRef 51 36 := ![.occ 19, .occ 20, .occ 21, .occ 22, .occ 23, .occ 24, .occ 25, .occ 26, .occ 27, .occ 28, .occ 29, .occ 30, .occ 31, .occ 32, .occ 33, .occ 34, .occ 35, .occ 36, .occ 37, .occ 38, .occ 39, .occ 40, .occ 41, .occ 42, .occ 43, .occ 44, .occ 45, .occ 46, .occ 47, .occ 48, .occ 49, .occ 50, .sumGe, .nonneg 8]

def plane428GenLeaf0000Mult : Fin 34 → Nat := ![5, 10, 1, 13, 3, 16, 4, 18, 18, 6, 8, 10, 20, 12, 8, 16, 16, 10, 6, 10, 8, 10, 6, 10, 6, 10, 6, 10, 4, 4, 6, 6, 32, 12]

theorem plane428GenLeaf0000 (x : Fin 36 → Int)
    (hroot : plane428GenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane428GenLeaf0000Refs i).resolveCoeff plane428GenOccSys j)
    (fun i => (plane428GenLeaf0000Refs i).resolveRhs plane428GenOccSys) plane428GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane428GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 19
  · exact hroot.hOcc 20
  · exact hroot.hOcc 21
  · exact hroot.hOcc 22
  · exact hroot.hOcc 23
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
  · change (∑ j, (-1 : Int) * x j) ≤ -plane428GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 36) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8

end QiushiMatmul
