import QiushiPlane282GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane282GenLeaf0000Refs : Fin 19 → RowRef 100 28 := ![.occ 4, .occ 9, .occ 20, .occ 41, .occ 44, .occ 47, .occ 48, .occ 52, .occ 58, .occ 60, .occ 61, .occ 62, .occ 63, .occ 65, .occ 74, .occ 76, .occ 88, .sumGe, .branchLe 4 (0)]

def plane282GenLeaf0000Mult : Fin 19 → Nat := ![6, 6, 4, 1, 2, 2, 2, 2, 1, 2, 1, 2, 3, 2, 3, 1, 2, 8, 8]

theorem plane282GenLeaf0000 (x : Fin 28 → Int)
    (hroot : plane282GenOccSys.RootHolds x)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane282GenLeaf0000Refs i).resolveCoeff plane282GenOccSys j)
    (fun i => (plane282GenLeaf0000Refs i).resolveRhs plane282GenOccSys) plane282GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane282GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 4
  · exact hroot.hOcc 9
  · exact hroot.hOcc 20
  · exact hroot.hOcc 41
  · exact hroot.hOcc 44
  · exact hroot.hOcc 47
  · exact hroot.hOcc 48
  · exact hroot.hOcc 52
  · exact hroot.hOcc 58
  · exact hroot.hOcc 60
  · exact hroot.hOcc 61
  · exact hroot.hOcc 62
  · exact hroot.hOcc 63
  · exact hroot.hOcc 65
  · exact hroot.hOcc 74
  · exact hroot.hOcc 76
  · exact hroot.hOcc 88
  · change (∑ j, (-1 : Int) * x j) ≤ -plane282GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (4 : Fin 28) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4

end QiushiMatmul
