import QiushiGlobalOrbitUnused181CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane181UnusedGenIndicatorBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 13,
    plane181UnusedGenIndicatorProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane181UnusedGenIndicatorProperty, plane181UnusedGenConfig, plane181UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
