import QiushiPlaneOrbitClassification

namespace QiushiMatmul.PlaneOrbit.FullClassification

example : Nat.card {W : Space // Equivalent (frozenRep 0) W} = 98 := exact_orbit_sizes 0
example : sizes 0 = sizes 6 := rfl
example : ¬ Equivalent (frozenRep 0) (frozenRep 6) :=
  representatives_inequivalent 0 6 (by decide)
example (W : Space) (hW : Module.finrank F2 W = 2) :
    ∃! i : Fin 14, Equivalent (frozenRep i) W := classification W hW

#check exact_orbit_sizes
#check representatives_inequivalent
#check classification
#check orbit_count
#print axioms exact_orbit_sizes
#print axioms representatives_inequivalent
#print axioms classification
#print axioms orbit_count

end QiushiMatmul.PlaneOrbit.FullClassification
