import QiushiPlane485GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane485GenLeaf0008Refs : Fin 42 → RowRef 421 41 := ![.occ 87, .occ 95, .occ 106, .occ 107, .occ 155, .occ 164, .occ 175, .occ 179, .occ 184, .occ 198, .occ 204, .occ 217, .occ 218, .occ 224, .occ 228, .occ 229, .occ 240, .occ 246, .occ 262, .occ 271, .occ 276, .occ 304, .occ 305, .occ 353, .occ 359, .occ 362, .occ 368, .occ 374, .occ 393, .occ 403, .occ 409, .sumGe, .nonneg 7, .nonneg 12, .branchLe 28 (0), .branchLe 21 (0), .branchLe 14 (0), .branchLe 11 (0), .branchGe 39 (1), .branchGe 29 (1), .branchLe 25 (0), .branchLe 6 (0)]

def plane485GenLeaf0008Mult : Fin 42 → Nat := ![14949, 6363, 17302, 24857, 10803, 7635, 7774, 8285, 3764, 215, 9463, 7895, 2550, 12627, 7451, 11187, 10182, 7863, 7905, 4547, 2491, 7951, 646, 486, 692, 6727, 7079, 11875, 249, 5769, 612, 33454, 1525, 7213, 23825, 20827, 29690, 26115, 44087, 108394, 19210, 18707]

theorem plane485GenLeaf0008 (x : Fin 41 → Int)
    (hroot : plane485GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane485GenLeaf0008Refs i).resolveCoeff plane485GenOccSys j)
    (fun i => (plane485GenLeaf0008Refs i).resolveRhs plane485GenOccSys) plane485GenLeaf0008Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane485GenLeaf0008Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 95
  · exact hroot.hOcc 106
  · exact hroot.hOcc 107
  · exact hroot.hOcc 155
  · exact hroot.hOcc 164
  · exact hroot.hOcc 175
  · exact hroot.hOcc 179
  · exact hroot.hOcc 184
  · exact hroot.hOcc 198
  · exact hroot.hOcc 204
  · exact hroot.hOcc 217
  · exact hroot.hOcc 218
  · exact hroot.hOcc 224
  · exact hroot.hOcc 228
  · exact hroot.hOcc 229
  · exact hroot.hOcc 240
  · exact hroot.hOcc 246
  · exact hroot.hOcc 262
  · exact hroot.hOcc 271
  · exact hroot.hOcc 276
  · exact hroot.hOcc 304
  · exact hroot.hOcc 305
  · exact hroot.hOcc 353
  · exact hroot.hOcc 359
  · exact hroot.hOcc 362
  · exact hroot.hOcc 368
  · exact hroot.hOcc 374
  · exact hroot.hOcc 393
  · exact hroot.hOcc 403
  · exact hroot.hOcc 409
  · change (∑ j, (-1 : Int) * x j) ≤ -plane485GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (12 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (28 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (21 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (14 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (11 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (39 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (29 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (25 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (6 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6

end QiushiMatmul
