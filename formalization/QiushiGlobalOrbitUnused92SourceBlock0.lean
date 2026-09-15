import QiushiGlobalOrbitUnused92CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane92UnusedGenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 11,
    plane92UnusedGenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane92UnusedGenSourceProperty, plane92UnusedGenConfig, plane92UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
