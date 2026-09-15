import QiushiGlobalOrbitUnused353Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane353UnusedGenLeaf0000Refs : Fin 20 → RowRef 39 20 := ![.occ 0, .occ 2, .occ 10, .occ 15, .occ 16, .occ 17, .occ 22, .occ 23, .occ 24, .occ 25, .occ 26, .occ 27, .occ 28, .occ 30, .occ 31, .occ 34, .occ 35, .occ 38, .sumGe, .branchLe 15 (0)]

def plane353UnusedGenLeaf0000Mult : Fin 20 → Nat := ![6, 4, 4, 2, 3, 1, 1, 1, 3, 2, 3, 2, 5, 1, 2, 2, 3, 4, 11, 8]

theorem plane353UnusedGenLeaf0000 (x : Fin 20 → Int)
    (hroot : plane353UnusedGenOccSys.RootHolds x)
    (hUB_15 : x 15 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane353UnusedGenLeaf0000Refs i).resolveCoeff plane353UnusedGenOccSys j)
    (fun i => (plane353UnusedGenLeaf0000Refs i).resolveRhs plane353UnusedGenOccSys) plane353UnusedGenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane353UnusedGenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 2
  · exact hroot.hOcc 10
  · exact hroot.hOcc 15
  · exact hroot.hOcc 16
  · exact hroot.hOcc 17
  · exact hroot.hOcc 22
  · exact hroot.hOcc 23
  · exact hroot.hOcc 24
  · exact hroot.hOcc 25
  · exact hroot.hOcc 26
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · exact hroot.hOcc 30
  · exact hroot.hOcc 31
  · exact hroot.hOcc 34
  · exact hroot.hOcc 35
  · exact hroot.hOcc 38
  · change (∑ j, (-1 : Int) * x j) ≤ -plane353UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 20) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15

end QiushiMatmul
