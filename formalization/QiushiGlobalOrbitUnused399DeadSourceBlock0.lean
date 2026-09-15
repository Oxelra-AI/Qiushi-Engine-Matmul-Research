import QiushiGlobalOrbitUnused399CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane399UnusedGenDeadSourceBlock0 : forall offset : Fin 128,
    forall hlt : 0 * 128 + offset.val < 18,
    plane399UnusedGenDeadSourceProperty (Fin.mk (0 * 128 + offset.val) hlt) := by
  simp only [plane399UnusedGenDeadSourceProperty, plane399UnusedGenConfig, plane399UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
