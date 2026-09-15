import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0071Refs : Fin 48 → RowRef 668 48 := ![.occ 82, .occ 83, .occ 94, .occ 101, .occ 164, .occ 190, .occ 193, .occ 211, .occ 216, .occ 217, .occ 219, .occ 223, .occ 239, .occ 241, .occ 246, .occ 256, .occ 260, .occ 281, .occ 312, .occ 315, .occ 343, .occ 368, .occ 370, .occ 390, .occ 392, .occ 399, .occ 423, .occ 444, .occ 479, .occ 483, .occ 531, .occ 546, .occ 566, .occ 567, .occ 594, .occ 619, .occ 639, .occ 641, .occ 648, .occ 650, .sumGe, .branchGe 39 (1), .branchLe 7 (0), .branchLe 28 (0), .branchLe 40 (0), .branchGe 29 (1), .branchLe 10 (0), .branchGe 12 (1)]

def plane487GenLeaf0071Mult : Fin 48 → Nat := ![18960, 1606, 33663, 8676, 51501, 124336, 16395, 24003, 7962, 20333, 31953, 28981, 108068, 33374, 3273, 5392, 4989, 18114, 77880, 4879, 42466, 14522, 35917, 21180, 1616, 15715, 7103, 20531, 793, 6557, 23683, 5371, 51223, 4609, 9768, 5178, 37493, 32195, 29043, 4879, 146321, 172638, 85443, 38253, 145528, 490544, 106729, 366462]

theorem plane487GenLeaf0071 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0071Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0071Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0071Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0071Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 82
  · exact hroot.hOcc 83
  · exact hroot.hOcc 94
  · exact hroot.hOcc 101
  · exact hroot.hOcc 164
  · exact hroot.hOcc 190
  · exact hroot.hOcc 193
  · exact hroot.hOcc 211
  · exact hroot.hOcc 216
  · exact hroot.hOcc 217
  · exact hroot.hOcc 219
  · exact hroot.hOcc 223
  · exact hroot.hOcc 239
  · exact hroot.hOcc 241
  · exact hroot.hOcc 246
  · exact hroot.hOcc 256
  · exact hroot.hOcc 260
  · exact hroot.hOcc 281
  · exact hroot.hOcc 312
  · exact hroot.hOcc 315
  · exact hroot.hOcc 343
  · exact hroot.hOcc 368
  · exact hroot.hOcc 370
  · exact hroot.hOcc 390
  · exact hroot.hOcc 392
  · exact hroot.hOcc 399
  · exact hroot.hOcc 423
  · exact hroot.hOcc 444
  · exact hroot.hOcc 479
  · exact hroot.hOcc 483
  · exact hroot.hOcc 531
  · exact hroot.hOcc 546
  · exact hroot.hOcc 566
  · exact hroot.hOcc 567
  · exact hroot.hOcc 594
  · exact hroot.hOcc 619
  · exact hroot.hOcc 639
  · exact hroot.hOcc 641
  · exact hroot.hOcc 648
  · exact hroot.hOcc 650
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (39 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (7 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (28 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (40 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (29 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (10 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (12 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12

end QiushiMatmul
