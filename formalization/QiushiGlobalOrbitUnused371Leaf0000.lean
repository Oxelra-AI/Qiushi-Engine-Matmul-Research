import QiushiGlobalOrbitUnused371Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane371UnusedGenLeaf0000Refs : Fin 16 → RowRef 38 18 := ![.occ 11, .occ 16, .occ 17, .occ 21, .occ 22, .occ 27, .occ 28, .occ 30, .occ 31, .occ 33, .occ 34, .occ 35, .occ 36, .occ 37, .sumGe, .branchLe 0 (1)]

def plane371UnusedGenLeaf0000Mult : Fin 16 → Nat := ![2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 4]

theorem plane371UnusedGenLeaf0000 (x : Fin 18 → Int)
    (hroot : plane371UnusedGenOccSys.RootHolds x)
    (hUB_0 : x 0 ≤ (1 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane371UnusedGenLeaf0000Refs i).resolveCoeff plane371UnusedGenOccSys j)
    (fun i => (plane371UnusedGenLeaf0000Refs i).resolveRhs plane371UnusedGenOccSys) plane371UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane371UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 11
  · exact hroot.hOcc 16
  · exact hroot.hOcc 17
  · exact hroot.hOcc 21
  · exact hroot.hOcc 22
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · exact hroot.hOcc 30
  · exact hroot.hOcc 31
  · exact hroot.hOcc 33
  · exact hroot.hOcc 34
  · exact hroot.hOcc 35
  · exact hroot.hOcc 36
  · exact hroot.hOcc 37
  · change (∑ j, (-1 : Int) * x j) ≤ -plane371UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 18) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_0

end QiushiMatmul
