import QiushiGlobalOrbitCoverage

namespace QiushiMatmul.GlobalOrbit
open PlaneOrbit

example (W : Submodule F2 Mat3) : ∃ i : Fin 496, frozenWangTable.OrbitImage i W :=
  frozen_coverage W
example : Covered (⊤ : Space) := frozen_coverage _
example : Covered (⊥ : Space) := frozen_coverage _
example (i : Fin 496) : Covered (dual (representative i)) := frozen_annihilators_covered i
example (d : Fin 10) (W : Space) (hW : Module.finrank F2 W = d.val) : Covered W :=
  all_dimensions_covered d.val W hW

#print axioms frozen_coverage
#print axioms frozen_annihilators_covered

end QiushiMatmul.GlobalOrbit
