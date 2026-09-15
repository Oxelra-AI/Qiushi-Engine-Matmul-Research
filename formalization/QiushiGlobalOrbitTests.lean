import QiushiGlobalOrbitCertificate
import QiushiGlobalOrbitExtension

namespace QiushiMatmul.GlobalOrbit
open PlaneOrbit

example : Covered (⊥ : Space) := zero_covered
example (W V : Space) : Equivalent (dual W) (dual V) ↔ Equivalent W V :=
  dual_equivalent_iff W V
example (h : ExtensionChecks) (W : Space) :
    ∃ i : Fin 496, frozenWangTable.OrbitImage i W := coverage_of_extensions h W
example : ¬ BasisCheck [1, 1] [1, 1] := by decide +kernel

#check dual_dimension
#check dual_equivalent_iff
#check coverage_of_low_dimensions
#check coverage_of_extensions
#check global_coverage_iff_extensions
#print axioms dual_equivalent_iff
#print axioms coverage_of_low_dimensions
#print axioms coverage_of_extensions
#print axioms global_coverage_iff_extensions
#print axioms basis_dimension
#print axioms dual_eq_word

end QiushiMatmul.GlobalOrbit
