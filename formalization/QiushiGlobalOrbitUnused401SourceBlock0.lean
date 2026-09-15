import QiushiGlobalOrbitUnused401CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane401UnusedGenSourceBlock0 : forall offset : Fin 128,
    forall hlt : 0 * 128 + offset.val < 30,
    plane401UnusedGenSourceProperty (Fin.mk (0 * 128 + offset.val) hlt) := by
  simp only [plane401UnusedGenSourceProperty, plane401UnusedGenConfig, plane401UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
