import QiushiGlobalOrbitUnused371CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane371UnusedGenSourceBlock0 : forall offset : Fin 128,
    forall hlt : 0 * 128 + offset.val < 38,
    plane371UnusedGenSourceProperty (Fin.mk (0 * 128 + offset.val) hlt) := by
  simp only [plane371UnusedGenSourceProperty, plane371UnusedGenConfig, plane371UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
