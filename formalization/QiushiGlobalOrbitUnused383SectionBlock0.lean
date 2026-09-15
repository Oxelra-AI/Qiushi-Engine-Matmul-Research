import QiushiGlobalOrbitUnused383CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane383UnusedGenSectionBlock0 : forall offset : Fin 128,
    forall hlt : 0 * 128 + offset.val < 512,
    plane383UnusedGenSectionProperty (Fin.mk (0 * 128 + offset.val) hlt) := by
  simp only [plane383UnusedGenSectionProperty, plane383UnusedGenConfig, plane383UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
