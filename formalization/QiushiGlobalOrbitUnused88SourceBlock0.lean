import QiushiGlobalOrbitUnused88CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane88UnusedGenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 13,
    plane88UnusedGenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane88UnusedGenSourceProperty, plane88UnusedGenConfig, plane88UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
