import QiushiGlobalOrbitUnused355Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane355UnusedGenLeaf0000Refs : Fin 14 → RowRef 21 22 := ![.occ 0, .occ 10, .occ 11, .occ 12, .occ 13, .occ 14, .occ 15, .occ 16, .occ 17, .occ 18, .occ 19, .occ 20, .sumGe, .nonneg 0]

def plane355UnusedGenLeaf0000Mult : Fin 14 → Nat := ![3, 3, 3, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1]

theorem plane355UnusedGenLeaf0000 (x : Fin 22 → Int)
    (hroot : plane355UnusedGenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane355UnusedGenLeaf0000Refs i).resolveCoeff plane355UnusedGenOccSys j)
    (fun i => (plane355UnusedGenLeaf0000Refs i).resolveRhs plane355UnusedGenOccSys) plane355UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane355UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 10
  · exact hroot.hOcc 11
  · exact hroot.hOcc 12
  · exact hroot.hOcc 13
  · exact hroot.hOcc 14
  · exact hroot.hOcc 15
  · exact hroot.hOcc 16
  · exact hroot.hOcc 17
  · exact hroot.hOcc 18
  · exact hroot.hOcc 19
  · exact hroot.hOcc 20
  · change (∑ j, (-1 : Int) * x j) ≤ -plane355UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 22) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0

end QiushiMatmul
