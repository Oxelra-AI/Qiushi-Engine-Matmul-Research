import QiushiPlaneOrbitClassification
import QiushiPlaneOrbitNormalForm

/-! The report classification stated in the frozen table's existing direct-action API. -/
open Matrix
namespace QiushiMatmul.PlaneOrbit.FullClassification

theorem frozen_orbit_image_iff (i : Fin 14) (W : Space) :
    frozenWangTable.OrbitImage ⟨478 + i.val, by omega⟩ W ↔ Equivalent (frozenRep i) W := by
  rw [equivalent_iff_transport]
  constructor
  · rintro ⟨P, Q, ⟨hP⟩, ⟨hQ⟩, tr, he⟩
    let := hP
    let := hQ
    exact ⟨P, Q, Matrix.isUnit_det_of_invertible _, Matrix.isUnit_det_of_invertible _, tr, he⟩
  · rintro ⟨P, Q, hP, hQ, tr, he⟩
    exact ⟨P, Q, ⟨Matrix.invertibleOfIsUnitDet P hP⟩,
      ⟨Matrix.invertibleOfIsUnitDet Q hQ⟩, tr, he⟩

theorem frozen_classification (W : Space) (hW : Module.finrank F2 W = 2) :
    ∃! i : Fin 14, frozenWangTable.OrbitImage ⟨478 + i.val, by omega⟩ W := by
  simpa only [frozen_orbit_image_iff] using classification W hW

theorem frozen_orbit_sizes (i : Fin 14) :
    Nat.card {W : Space // frozenWangTable.OrbitImage ⟨478 + i.val, by omega⟩ W} = sizes i := by
  simp_rw [frozen_orbit_image_iff]
  exact exact_orbit_sizes i

theorem frozen_representatives_inequivalent (i j : Fin 14) (hij : i ≠ j) :
    ¬ frozenWangTable.OrbitImage ⟨478 + i.val, by omega⟩ (frozenRep j) := by
  rw [frozen_orbit_image_iff]
  exact representatives_inequivalent i j hij

#check frozen_classification
#check frozen_orbit_sizes
#check frozen_representatives_inequivalent
#print axioms equivalent_iff_transport
#print axioms frozen_classification
#print axioms frozen_orbit_sizes
#print axioms frozen_representatives_inequivalent

end QiushiMatmul.PlaneOrbit.FullClassification
