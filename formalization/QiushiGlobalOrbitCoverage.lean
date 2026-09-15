import QiushiGlobalOrbitChecks0
import QiushiGlobalOrbitChecks1
import QiushiGlobalOrbitChecks2
import QiushiGlobalOrbitChecks3
import QiushiGlobalOrbitChecks4
import QiushiGlobalOrbitChecks5
import QiushiGlobalOrbitChecks6
import QiushiGlobalOrbitChecks7
import QiushiGlobalOrbitChecks8
import QiushiGlobalOrbitChecks9
import QiushiGlobalOrbitChecks10
import QiushiGlobalOrbitChecks11
import QiushiGlobalOrbitChecks12
import QiushiGlobalOrbitChecks13
import QiushiGlobalOrbitChecks14
import QiushiGlobalOrbitChecks15
import QiushiGlobalOrbitChecks16
import QiushiGlobalOrbitChecks17
import QiushiGlobalOrbitChecks18
import QiushiGlobalOrbitChecks19
import QiushiGlobalOrbitChecks20
import QiushiGlobalOrbitChecks21
import QiushiGlobalOrbitChecks22
import QiushiGlobalOrbitChecks23
import QiushiGlobalOrbitChecks24
import QiushiGlobalOrbitChecks25
import QiushiGlobalOrbitChecks26
import QiushiGlobalOrbitChecks27
import QiushiGlobalOrbitChecks28
import QiushiGlobalOrbitChecks29
import QiushiGlobalOrbitChecks30

namespace QiushiMatmul.GlobalOrbit
open PlaneOrbit
set_option maxHeartbeats 4000000

theorem extension_checks : ExtensionChecks := by
  have block (b : Fin 31) : ∀ j : Fin 16, ∀ c : Fin 512,
      Covered (spanCodes (c.val :: frozenWangBasis
        ⟨16 * b.val + j.val, by omega⟩)) := by
    fin_cases b
    · exact Cases0.covered
    · exact Cases1.covered
    · exact Cases2.covered
    · exact Cases3.covered
    · exact Cases4.covered
    · exact Cases5.covered
    · exact Cases6.covered
    · exact Cases7.covered
    · exact Cases8.covered
    · exact Cases9.covered
    · exact Cases10.covered
    · exact Cases11.covered
    · exact Cases12.covered
    · exact Cases13.covered
    · exact Cases14.covered
    · exact Cases15.covered
    · exact Cases16.covered
    · exact Cases17.covered
    · exact Cases18.covered
    · exact Cases19.covered
    · exact Cases20.covered
    · exact Cases21.covered
    · exact Cases22.covered
    · exact Cases23.covered
    · exact Cases24.covered
    · exact Cases25.covered
    · exact Cases26.covered
    · exact Cases27.covered
    · exact Cases28.covered
    · exact Cases29.covered
    · exact Cases30.covered
  intro i c
  let b : Fin 31 := ⟨i.val / 16, by omega⟩
  let j : Fin 16 := ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩
  have he : 16 * b.val + j.val = i.val := Nat.div_add_mod i.val 16
  have h := block b j c
  simpa only [he] using h

/-- Every actual matrix subspace lies in one of the 496 frozen direct-action orbits. -/
theorem frozen_coverage (W : Space) :
    ∃ i : Fin 496, frozenWangTable.OrbitImage i W := coverage_of_extensions extension_checks W

theorem all_dimensions_covered (d : Nat) : CoversDimension d := fun W _ => frozen_coverage W

theorem frozen_annihilators_covered (i : Fin 496) : Covered (dual (representative i)) :=
  frozen_coverage _

#check frozen_coverage
#check all_dimensions_covered
#print axioms extension_checks
#print axioms frozen_coverage
#print axioms all_dimensions_covered

end QiushiMatmul.GlobalOrbit
