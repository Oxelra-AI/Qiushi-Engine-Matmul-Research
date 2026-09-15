import QiushiGlobalOrbitUnused389CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane389UnusedGenIndicatorBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 35,
    plane389UnusedGenIndicatorProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane389UnusedGenIndicatorProperty, plane389UnusedGenConfig, plane389UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
