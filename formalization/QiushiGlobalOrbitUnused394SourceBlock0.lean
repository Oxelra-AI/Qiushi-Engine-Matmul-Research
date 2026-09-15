import QiushiGlobalOrbitUnused394CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane394UnusedGenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 32,
    plane394UnusedGenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane394UnusedGenSourceProperty, plane394UnusedGenConfig, plane394UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
