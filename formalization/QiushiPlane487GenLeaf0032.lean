import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0032Refs : Fin 49 → RowRef 668 48 := ![.occ 83, .occ 86, .occ 111, .occ 178, .occ 206, .occ 216, .occ 218, .occ 219, .occ 220, .occ 224, .occ 227, .occ 240, .occ 246, .occ 263, .occ 280, .occ 296, .occ 325, .occ 333, .occ 334, .occ 347, .occ 350, .occ 353, .occ 356, .occ 378, .occ 386, .occ 399, .occ 415, .occ 469, .occ 528, .occ 529, .occ 546, .occ 572, .occ 593, .occ 613, .occ 653, .occ 661, .occ 662, .occ 665, .sumGe, .nonneg 20, .nonneg 25, .nonneg 39, .branchLe 23 (0), .branchGe 6 (1), .branchGe 33 (1), .branchLe 12 (0), .branchLe 42 (0), .branchLe 36 (0), .branchGe 19 (1)]

def plane487GenLeaf0032Mult : Fin 49 → Nat := ![38099, 79958, 48669, 260762, 79853, 4895, 37025, 30025, 83261, 196301, 262648, 50527, 34847, 15316, 118365, 313133, 15294, 35234, 17622, 83919, 61722, 97801, 169883, 12328, 167161, 26286, 128454, 8607, 17045, 176521, 88849, 33599, 18195, 6232, 59513, 42840, 53370, 138492, 485901, 472174, 70084, 73684, 97903, 950614, 968411, 477294, 274497, 146482, 1037386]

theorem plane487GenLeaf0032 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_33 : (1 : Int) ≤ x 33)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0032Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0032Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0032Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0032Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 83
  · exact hroot.hOcc 86
  · exact hroot.hOcc 111
  · exact hroot.hOcc 178
  · exact hroot.hOcc 206
  · exact hroot.hOcc 216
  · exact hroot.hOcc 218
  · exact hroot.hOcc 219
  · exact hroot.hOcc 220
  · exact hroot.hOcc 224
  · exact hroot.hOcc 227
  · exact hroot.hOcc 240
  · exact hroot.hOcc 246
  · exact hroot.hOcc 263
  · exact hroot.hOcc 280
  · exact hroot.hOcc 296
  · exact hroot.hOcc 325
  · exact hroot.hOcc 333
  · exact hroot.hOcc 334
  · exact hroot.hOcc 347
  · exact hroot.hOcc 350
  · exact hroot.hOcc 353
  · exact hroot.hOcc 356
  · exact hroot.hOcc 378
  · exact hroot.hOcc 386
  · exact hroot.hOcc 399
  · exact hroot.hOcc 415
  · exact hroot.hOcc 469
  · exact hroot.hOcc 528
  · exact hroot.hOcc 529
  · exact hroot.hOcc 546
  · exact hroot.hOcc 572
  · exact hroot.hOcc 593
  · exact hroot.hOcc 613
  · exact hroot.hOcc 653
  · exact hroot.hOcc 661
  · exact hroot.hOcc 662
  · exact hroot.hOcc 665
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (20 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (25 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (39 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (6 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (33 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_33
  · change (∑ k, (if k = (12 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (42 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (36 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (19 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19

end QiushiMatmul
