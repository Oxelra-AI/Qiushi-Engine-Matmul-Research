import QiushiGlobalOrbitUnused372Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane372UnusedGenLeaf0000Refs : Fin 27 → RowRef 37 26 := ![.occ 0, .occ 1, .occ 2, .occ 4, .occ 5, .occ 7, .occ 11, .occ 12, .occ 14, .occ 15, .occ 16, .occ 18, .occ 19, .occ 21, .occ 22, .occ 24, .occ 25, .occ 30, .occ 31, .occ 32, .occ 33, .occ 34, .occ 35, .occ 36, .sumGe, .nonneg 19, .branchLe 25 (0)]

def plane372UnusedGenLeaf0000Mult : Fin 27 → Nat := ![34, 81, 53, 38, 28, 60, 20, 29, 19, 27, 10, 35, 22, 10, 28, 9, 29, 5, 3, 20, 9, 29, 5, 18, 81, 23, 81]

theorem plane372UnusedGenLeaf0000 (x : Fin 26 → Int)
    (hroot : plane372UnusedGenOccSys.RootHolds x)
    (hUB_25 : x 25 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane372UnusedGenLeaf0000Refs i).resolveCoeff plane372UnusedGenOccSys j)
    (fun i => (plane372UnusedGenLeaf0000Refs i).resolveRhs plane372UnusedGenOccSys) plane372UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane372UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 1
  · exact hroot.hOcc 2
  · exact hroot.hOcc 4
  · exact hroot.hOcc 5
  · exact hroot.hOcc 7
  · exact hroot.hOcc 11
  · exact hroot.hOcc 12
  · exact hroot.hOcc 14
  · exact hroot.hOcc 15
  · exact hroot.hOcc 16
  · exact hroot.hOcc 18
  · exact hroot.hOcc 19
  · exact hroot.hOcc 21
  · exact hroot.hOcc 22
  · exact hroot.hOcc 24
  · exact hroot.hOcc 25
  · exact hroot.hOcc 30
  · exact hroot.hOcc 31
  · exact hroot.hOcc 32
  · exact hroot.hOcc 33
  · exact hroot.hOcc 34
  · exact hroot.hOcc 35
  · exact hroot.hOcc 36
  · change (∑ j, (-1 : Int) * x j) ≤ -plane372UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (19 : Fin 26) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (25 : Fin 26) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25

end QiushiMatmul
