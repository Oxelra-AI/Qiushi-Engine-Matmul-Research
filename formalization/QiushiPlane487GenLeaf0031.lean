import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0031Refs : Fin 49 → RowRef 668 48 := ![.occ 89, .occ 92, .occ 95, .occ 101, .occ 111, .occ 153, .occ 178, .occ 217, .occ 218, .occ 219, .occ 240, .occ 246, .occ 256, .occ 274, .occ 294, .occ 296, .occ 299, .occ 303, .occ 333, .occ 347, .occ 356, .occ 381, .occ 386, .occ 387, .occ 391, .occ 404, .occ 407, .occ 410, .occ 472, .occ 474, .occ 478, .occ 529, .occ 533, .occ 539, .occ 563, .occ 590, .occ 593, .occ 599, .occ 631, .occ 639, .sumGe, .branchLe 39 (0), .branchLe 23 (0), .branchGe 6 (1), .branchGe 33 (1), .branchLe 12 (0), .branchLe 42 (0), .branchLe 36 (0), .branchLe 19 (0)]

def plane487GenLeaf0031Mult : Fin 49 → Nat := ![605836, 73825, 132458, 95739, 569655, 189506, 185155, 16279, 227878, 45742, 47351, 130117, 43167, 167825, 225243, 387689, 105548, 81288, 189434, 200788, 167027, 13951, 307821, 24759, 65917, 148713, 93383, 9371, 121622, 162324, 85195, 139678, 157037, 68376, 42997, 9371, 142823, 74023, 137875, 2295, 745514, 441217, 454066, 2196353, 2204674, 743219, 66392, 208161, 603541]

theorem plane487GenLeaf0031 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_33 : (1 : Int) ≤ x 33)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0031Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0031Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0031Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0031Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 89
  · exact hroot.hOcc 92
  · exact hroot.hOcc 95
  · exact hroot.hOcc 101
  · exact hroot.hOcc 111
  · exact hroot.hOcc 153
  · exact hroot.hOcc 178
  · exact hroot.hOcc 217
  · exact hroot.hOcc 218
  · exact hroot.hOcc 219
  · exact hroot.hOcc 240
  · exact hroot.hOcc 246
  · exact hroot.hOcc 256
  · exact hroot.hOcc 274
  · exact hroot.hOcc 294
  · exact hroot.hOcc 296
  · exact hroot.hOcc 299
  · exact hroot.hOcc 303
  · exact hroot.hOcc 333
  · exact hroot.hOcc 347
  · exact hroot.hOcc 356
  · exact hroot.hOcc 381
  · exact hroot.hOcc 386
  · exact hroot.hOcc 387
  · exact hroot.hOcc 391
  · exact hroot.hOcc 404
  · exact hroot.hOcc 407
  · exact hroot.hOcc 410
  · exact hroot.hOcc 472
  · exact hroot.hOcc 474
  · exact hroot.hOcc 478
  · exact hroot.hOcc 529
  · exact hroot.hOcc 533
  · exact hroot.hOcc 539
  · exact hroot.hOcc 563
  · exact hroot.hOcc 590
  · exact hroot.hOcc 593
  · exact hroot.hOcc 599
  · exact hroot.hOcc 631
  · exact hroot.hOcc 639
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (6 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (33 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_33
  · change (∑ k, (if k = (12 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (42 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (36 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (19 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19

end QiushiMatmul
