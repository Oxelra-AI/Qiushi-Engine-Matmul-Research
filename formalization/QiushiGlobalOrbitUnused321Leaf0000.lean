import QiushiGlobalOrbitUnused321Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane321UnusedGenLeaf0000Refs : Fin 23 → RowRef 49 26 := ![.occ 5, .occ 8, .occ 16, .occ 17, .occ 18, .occ 21, .occ 25, .occ 26, .occ 27, .occ 28, .occ 30, .occ 31, .occ 32, .occ 33, .occ 35, .occ 38, .occ 42, .occ 43, .occ 45, .occ 46, .sumGe, .branchLe 21 (0), .branchLe 9 (0)]

def plane321UnusedGenLeaf0000Mult : Fin 23 → Nat := ![10, 2, 10, 2, 20, 15, 1, 8, 3, 4, 2, 4, 8, 17, 6, 6, 4, 4, 14, 1, 31, 30, 30]

theorem plane321UnusedGenLeaf0000 (x : Fin 26 → Int)
    (hroot : plane321UnusedGenOccSys.RootHolds x)
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane321UnusedGenLeaf0000Refs i).resolveCoeff plane321UnusedGenOccSys j)
    (fun i => (plane321UnusedGenLeaf0000Refs i).resolveRhs plane321UnusedGenOccSys) plane321UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane321UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · exact hroot.hOcc 8
  · exact hroot.hOcc 16
  · exact hroot.hOcc 17
  · exact hroot.hOcc 18
  · exact hroot.hOcc 21
  · exact hroot.hOcc 25
  · exact hroot.hOcc 26
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · exact hroot.hOcc 30
  · exact hroot.hOcc 31
  · exact hroot.hOcc 32
  · exact hroot.hOcc 33
  · exact hroot.hOcc 35
  · exact hroot.hOcc 38
  · exact hroot.hOcc 42
  · exact hroot.hOcc 43
  · exact hroot.hOcc 45
  · exact hroot.hOcc 46
  · change (∑ j, (-1 : Int) * x j) ≤ -plane321UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (21 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (9 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9

end QiushiMatmul
