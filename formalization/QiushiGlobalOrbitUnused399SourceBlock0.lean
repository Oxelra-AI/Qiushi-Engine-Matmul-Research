import QiushiGlobalOrbitUnused399CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane399UnusedGenSourceBlock0 : forall offset : Fin 128,
    forall hlt : 0 * 128 + offset.val < 25,
    plane399UnusedGenSourceProperty (Fin.mk (0 * 128 + offset.val) hlt) := by
  simp only [plane399UnusedGenSourceProperty, plane399UnusedGenConfig, plane399UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
