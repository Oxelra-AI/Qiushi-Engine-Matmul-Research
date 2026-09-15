import QiushiGlobalOrbitUnused321Data
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane321UnusedGenLeaf0002Refs : Fin 27 → RowRef 49 26 := ![.occ 6, .occ 9, .occ 10, .occ 11, .occ 12, .occ 13, .occ 16, .occ 17, .occ 18, .occ 21, .occ 22, .occ 23, .occ 25, .occ 26, .occ 29, .occ 30, .occ 31, .occ 32, .occ 34, .occ 37, .occ 38, .occ 41, .occ 47, .occ 48, .sumGe, .nonneg 9, .branchGe 21 (1)]

def plane321UnusedGenLeaf0002Mult : Fin 27 → Nat := ![26, 22, 220, 246, 238, 46, 16, 70, 170, 43, 32, 253, 97, 62, 38, 156, 32, 142, 76, 140, 112, 50, 111, 67, 425, 6, 670]

theorem plane321UnusedGenLeaf0002 (x : Fin 26 → Int)
    (hroot : plane321UnusedGenOccSys.RootHolds x)
    (hLB_21 : (1 : Int) ≤ x 21)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane321UnusedGenLeaf0002Refs i).resolveCoeff plane321UnusedGenOccSys j)
    (fun i => (plane321UnusedGenLeaf0002Refs i).resolveRhs plane321UnusedGenOccSys) plane321UnusedGenLeaf0002Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane321UnusedGenLeaf0002Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 6
  · exact hroot.hOcc 9
  · exact hroot.hOcc 10
  · exact hroot.hOcc 11
  · exact hroot.hOcc 12
  · exact hroot.hOcc 13
  · exact hroot.hOcc 16
  · exact hroot.hOcc 17
  · exact hroot.hOcc 18
  · exact hroot.hOcc 21
  · exact hroot.hOcc 22
  · exact hroot.hOcc 23
  · exact hroot.hOcc 25
  · exact hroot.hOcc 26
  · exact hroot.hOcc 29
  · exact hroot.hOcc 30
  · exact hroot.hOcc 31
  · exact hroot.hOcc 32
  · exact hroot.hOcc 34
  · exact hroot.hOcc 37
  · exact hroot.hOcc 38
  · exact hroot.hOcc 41
  · exact hroot.hOcc 47
  · exact hroot.hOcc 48
  · change (∑ j, (-1 : Int) * x j) ≤ -plane321UnusedGenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (9 : Fin 26) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 9
  · change (∑ k, (if k = (21 : Fin 26) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21

end QiushiMatmul
