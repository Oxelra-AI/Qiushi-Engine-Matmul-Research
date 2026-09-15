import QiushiGlobalOrbitUnused354CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane354UnusedGenIndicatorBlock0 : forall offset : Fin 128,
    forall hlt : 0 * 128 + offset.val < 30,
    plane354UnusedGenIndicatorProperty (Fin.mk (0 * 128 + offset.val) hlt) := by
  simp only [plane354UnusedGenIndicatorProperty, plane354UnusedGenConfig, plane354UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
