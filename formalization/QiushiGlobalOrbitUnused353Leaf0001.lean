import QiushiGlobalOrbitUnused353Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane353UnusedGenLeaf0001Refs : Fin 17 → RowRef 39 20 := ![.occ 0, .occ 1, .occ 15, .occ 17, .occ 18, .occ 19, .occ 20, .occ 21, .occ 22, .occ 29, .occ 31, .occ 32, .occ 33, .occ 36, .occ 37, .sumGe, .branchGe 15 (1)]

def plane353UnusedGenLeaf0001Mult : Fin 17 → Nat := ![5, 1, 1, 1, 5, 2, 4, 1, 2, 6, 1, 3, 1, 1, 3, 6, 16]

theorem plane353UnusedGenLeaf0001 (x : Fin 20 → Int)
    (hroot : plane353UnusedGenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane353UnusedGenLeaf0001Refs i).resolveCoeff plane353UnusedGenOccSys j)
    (fun i => (plane353UnusedGenLeaf0001Refs i).resolveRhs plane353UnusedGenOccSys) plane353UnusedGenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane353UnusedGenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 1
  · exact hroot.hOcc 15
  · exact hroot.hOcc 17
  · exact hroot.hOcc 18
  · exact hroot.hOcc 19
  · exact hroot.hOcc 20
  · exact hroot.hOcc 21
  · exact hroot.hOcc 22
  · exact hroot.hOcc 29
  · exact hroot.hOcc 31
  · exact hroot.hOcc 32
  · exact hroot.hOcc 33
  · exact hroot.hOcc 36
  · exact hroot.hOcc 37
  · change (∑ j, (-1 : Int) * x j) ≤ -plane353UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 20) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15

end QiushiMatmul
