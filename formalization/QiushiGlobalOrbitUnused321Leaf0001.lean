import QiushiGlobalOrbitUnused321Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane321UnusedGenLeaf0001Refs : Fin 27 → RowRef 49 26 := ![.occ 5, .occ 7, .occ 8, .occ 12, .occ 14, .occ 15, .occ 18, .occ 19, .occ 20, .occ 21, .occ 23, .occ 24, .occ 25, .occ 26, .occ 30, .occ 32, .occ 36, .occ 38, .occ 39, .occ 40, .occ 43, .occ 44, .occ 47, .occ 48, .sumGe, .nonneg 21, .branchGe 9 (1)]

def plane321UnusedGenLeaf0001Mult : Fin 27 → Nat := ![16, 246, 70, 238, 26, 220, 170, 22, 46, 43, 253, 32, 97, 142, 156, 62, 50, 112, 76, 38, 32, 140, 111, 67, 425, 6, 670]

theorem plane321UnusedGenLeaf0001 (x : Fin 26 → Int)
    (hroot : plane321UnusedGenOccSys.RootHolds x)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hUB_21 : x 21 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane321UnusedGenLeaf0001Refs i).resolveCoeff plane321UnusedGenOccSys j)
    (fun i => (plane321UnusedGenLeaf0001Refs i).resolveRhs plane321UnusedGenOccSys) plane321UnusedGenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane321UnusedGenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · exact hroot.hOcc 7
  · exact hroot.hOcc 8
  · exact hroot.hOcc 12
  · exact hroot.hOcc 14
  · exact hroot.hOcc 15
  · exact hroot.hOcc 18
  · exact hroot.hOcc 19
  · exact hroot.hOcc 20
  · exact hroot.hOcc 21
  · exact hroot.hOcc 23
  · exact hroot.hOcc 24
  · exact hroot.hOcc 25
  · exact hroot.hOcc 26
  · exact hroot.hOcc 30
  · exact hroot.hOcc 32
  · exact hroot.hOcc 36
  · exact hroot.hOcc 38
  · exact hroot.hOcc 39
  · exact hroot.hOcc 40
  · exact hroot.hOcc 43
  · exact hroot.hOcc 44
  · exact hroot.hOcc 47
  · exact hroot.hOcc 48
  · change (∑ j, (-1 : Int) * x j) ≤ -plane321UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (21 : Fin 26) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (9 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9

end QiushiMatmul
