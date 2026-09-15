import QiushiGlobalOrbitUnused382CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane382UnusedGenSourceBlock0 : forall offset : Fin 128,
    forall hlt : 0 * 128 + offset.val < 23,
    plane382UnusedGenSourceProperty (Fin.mk (0 * 128 + offset.val) hlt) := by
  simp only [plane382UnusedGenSourceProperty, plane382UnusedGenConfig, plane382UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
