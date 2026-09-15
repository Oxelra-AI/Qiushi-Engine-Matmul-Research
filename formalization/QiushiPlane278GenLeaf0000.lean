import QiushiPlane278GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane278GenLeaf0000Refs : Fin 25 → RowRef 28 24 := ![.occ 7, .occ 8, .occ 9, .occ 10, .occ 11, .occ 12, .occ 13, .occ 14, .occ 15, .occ 16, .occ 17, .occ 18, .occ 19, .occ 20, .occ 21, .occ 22, .occ 23, .occ 24, .occ 25, .occ 27, .sumGe, .nonneg 1, .nonneg 5, .nonneg 19, .nonneg 23]

def plane278GenLeaf0000Mult : Fin 25 → Nat := ![159, 81, 215, 137, 71, 43, 157, 25, 160, 219, 41, 8, 119, 141, 87, 3, 169, 85, 112, 32, 528, 16, 80, 39, 121]

theorem plane278GenLeaf0000 (x : Fin 24 → Int)
    (hroot : plane278GenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane278GenLeaf0000Refs i).resolveCoeff plane278GenOccSys j)
    (fun i => (plane278GenLeaf0000Refs i).resolveRhs plane278GenOccSys) plane278GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane278GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 7
  · exact hroot.hOcc 8
  · exact hroot.hOcc 9
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
  · exact hroot.hOcc 21
  · exact hroot.hOcc 22
  · exact hroot.hOcc 23
  · exact hroot.hOcc 24
  · exact hroot.hOcc 25
  · exact hroot.hOcc 27
  · change (∑ j, (-1 : Int) * x j) ≤ -plane278GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (1 : Fin 24) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (5 : Fin 24) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (19 : Fin 24) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (23 : Fin 24) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23

end QiushiMatmul
