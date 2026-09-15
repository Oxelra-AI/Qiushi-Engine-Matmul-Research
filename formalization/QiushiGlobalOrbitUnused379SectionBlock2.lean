import QiushiGlobalOrbitUnused379CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane379UnusedGenSectionBlock2 : forall offset : Fin 128,
    forall hlt : 2 * 128 + offset.val < 512,
    plane379UnusedGenSectionProperty (Fin.mk (2 * 128 + offset.val) hlt) := by
  simp only [plane379UnusedGenSectionProperty, plane379UnusedGenConfig, plane379UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
