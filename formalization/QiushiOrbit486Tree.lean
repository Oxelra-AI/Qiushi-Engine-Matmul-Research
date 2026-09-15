
-- Auto-generated orbit 486 tree composition
-- 10 leaves composed by recursively inherited branch hypotheses

import Mathlib
import QiushiOrbit486Data
import QiushiOrbit486Leaf0000
import QiushiOrbit486Leaf0001
import QiushiOrbit486Leaf0002
import QiushiOrbit486Leaf0003
import QiushiOrbit486Leaf0004
import QiushiOrbit486Leaf0005
import QiushiOrbit486Leaf0006
import QiushiOrbit486Leaf0007
import QiushiOrbit486Leaf0008
import QiushiOrbit486Leaf0009

namespace QiushiMatmul

theorem orbit486_no_model (x : Fin 40 → Int)
    (hroot : S_486.RootHolds x) : False := by
  by_cases hbr0 : x ⟨13, by decide⟩ ≤ 0
  · -- left branch: x[13] ≤ 0
    by_cases hbr1 : x ⟨36, by decide⟩ ≤ 0
    · -- left branch: x[36] ≤ 0
      by_cases hbr2 : x ⟨14, by decide⟩ ≤ 0
      · -- left branch: x[14] ≤ 0
        by_cases hbr3 : x ⟨17, by decide⟩ ≤ 0
        · -- left branch: x[17] ≤ 0
          exact leaf0_infeasible_486 x hroot hbr0 hbr1 hbr2 hbr3
        · -- right branch: x[17] ≥ 1
          have hbr3 : (1 : Int) ≤ x ⟨17, by decide⟩ := by omega
          exact leaf1_infeasible_486 x hroot hbr0 hbr1 hbr2 hbr3
      · -- right branch: x[14] ≥ 1
        have hbr2 : (1 : Int) ≤ x ⟨14, by decide⟩ := by omega
        by_cases hbr3 : x ⟨31, by decide⟩ ≤ 0
        · -- left branch: x[31] ≤ 0
          exact leaf2_infeasible_486 x hroot hbr0 hbr1 hbr2 hbr3
        · -- right branch: x[31] ≥ 1
          have hbr3 : (1 : Int) ≤ x ⟨31, by decide⟩ := by omega
          exact leaf3_infeasible_486 x hroot hbr0 hbr1 hbr2 hbr3
    · -- right branch: x[36] ≥ 1
      have hbr1 : (1 : Int) ≤ x ⟨36, by decide⟩ := by omega
      by_cases hbr2 : x ⟨19, by decide⟩ ≤ 0
      · -- left branch: x[19] ≤ 0
        by_cases hbr3 : x ⟨29, by decide⟩ ≤ 0
        · -- left branch: x[29] ≤ 0
          exact leaf4_infeasible_486 x hroot hbr0 hbr1 hbr2 hbr3
        · -- right branch: x[29] ≥ 1
          have hbr3 : (1 : Int) ≤ x ⟨29, by decide⟩ := by omega
          exact leaf5_infeasible_486 x hroot hbr0 hbr1 hbr2 hbr3
      · -- right branch: x[19] ≥ 1
        have hbr2 : (1 : Int) ≤ x ⟨19, by decide⟩ := by omega
        exact leaf6_infeasible_486 x hroot hbr0 hbr1 hbr2
  · -- right branch: x[13] ≥ 1
    have hbr0 : (1 : Int) ≤ x ⟨13, by decide⟩ := by omega
    by_cases hbr1 : x ⟨24, by decide⟩ ≤ 0
    · -- left branch: x[24] ≤ 0
      by_cases hbr2 : x ⟨19, by decide⟩ ≤ 0
      · -- left branch: x[19] ≤ 0
        exact leaf7_infeasible_486 x hroot hbr0 hbr1 hbr2
      · -- right branch: x[19] ≥ 1
        have hbr2 : (1 : Int) ≤ x ⟨19, by decide⟩ := by omega
        exact leaf8_infeasible_486 x hroot hbr0 hbr1 hbr2
    · -- right branch: x[24] ≥ 1
      have hbr1 : (1 : Int) ≤ x ⟨24, by decide⟩ := by omega
      exact leaf9_infeasible_486 x hroot hbr0 hbr1

end QiushiMatmul
