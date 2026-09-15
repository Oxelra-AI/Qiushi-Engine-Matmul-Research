import QiushiGlobalOrbitUnused356Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane356UnusedGenLeaf0000Refs : Fin 18 → RowRef 27 20 := ![.occ 0, .occ 9, .occ 13, .occ 14, .occ 15, .occ 16, .occ 17, .occ 18, .occ 19, .occ 20, .occ 21, .occ 22, .occ 23, .occ 24, .occ 25, .occ 26, .sumGe, .nonneg 3]

def plane356UnusedGenLeaf0000Mult : Fin 18 → Nat := ![16, 2, 2, 8, 10, 4, 7, 1, 2, 6, 4, 4, 7, 5, 3, 9, 16, 2]

theorem plane356UnusedGenLeaf0000 (x : Fin 20 → Int)
    (hroot : plane356UnusedGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane356UnusedGenLeaf0000Refs i).resolveCoeff plane356UnusedGenOccSys j)
    (fun i => (plane356UnusedGenLeaf0000Refs i).resolveRhs plane356UnusedGenOccSys) plane356UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane356UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 9
  · exact hroot.hOcc 13
  · exact hroot.hOcc 14
  · exact hroot.hOcc 15
  · exact hroot.hOcc 16
  · exact hroot.hOcc 17
  · exact hroot.hOcc 18
  · exact hroot.hOcc 19
  · exact hroot.hOcc 20
  · exact hroot.hOcc 21
  · exact hroot.hOcc 22
  · exact hroot.hOcc 23
  · exact hroot.hOcc 24
  · exact hroot.hOcc 25
  · exact hroot.hOcc 26
  · change (∑ j, (-1 : Int) * x j) ≤ -plane356UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 20) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3

end QiushiMatmul
