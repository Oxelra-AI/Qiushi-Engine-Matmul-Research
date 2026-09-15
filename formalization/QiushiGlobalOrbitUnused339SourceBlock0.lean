import QiushiGlobalOrbitUnused339CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane339UnusedGenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 31,
    plane339UnusedGenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane339UnusedGenSourceProperty, plane339UnusedGenConfig, plane339UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
