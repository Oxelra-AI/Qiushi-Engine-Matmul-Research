import QiushiGlobalOrbitUnused378CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane378UnusedGenSourceBlock0 : forall offset : Fin 128,
    forall hlt : 0 * 128 + offset.val < 17,
    plane378UnusedGenSourceProperty (Fin.mk (0 * 128 + offset.val) hlt) := by
  simp only [plane378UnusedGenSourceProperty, plane378UnusedGenConfig, plane378UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
