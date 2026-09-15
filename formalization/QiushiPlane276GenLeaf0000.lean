import QiushiPlane276GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane276GenLeaf0000Refs : Fin 16 → RowRef 37 17 := ![.occ 16, .occ 17, .occ 18, .occ 21, .occ 22, .occ 24, .occ 25, .occ 26, .occ 27, .occ 28, .occ 29, .occ 30, .occ 31, .occ 33, .sumGe, .branchLe 2 (1)]

def plane276GenLeaf0000Mult : Fin 16 → Nat := ![2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 2, 7, 6]

theorem plane276GenLeaf0000 (x : Fin 17 → Int)
    (hroot : plane276GenOccSys.RootHolds x)
    (hUB_2 : x 2 ≤ (1 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane276GenLeaf0000Refs i).resolveCoeff plane276GenOccSys j)
    (fun i => (plane276GenLeaf0000Refs i).resolveRhs plane276GenOccSys) plane276GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane276GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 16
  · exact hroot.hOcc 17
  · exact hroot.hOcc 18
  · exact hroot.hOcc 21
  · exact hroot.hOcc 22
  · exact hroot.hOcc 24
  · exact hroot.hOcc 25
  · exact hroot.hOcc 26
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · exact hroot.hOcc 29
  · exact hroot.hOcc 30
  · exact hroot.hOcc 31
  · exact hroot.hOcc 33
  · change (∑ j, (-1 : Int) * x j) ≤ -plane276GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 17) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_2

end QiushiMatmul
