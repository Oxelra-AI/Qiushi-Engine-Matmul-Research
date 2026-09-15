import QiushiGlobalOrbitUnused240CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane240UnusedGenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 15,
    plane240UnusedGenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane240UnusedGenSourceProperty, plane240UnusedGenConfig, plane240UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
