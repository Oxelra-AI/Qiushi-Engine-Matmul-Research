import QiushiGlobalOrbitUnused88CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane88UnusedGenSectionBlock10 : forall offset : Fin 32,
    forall hlt : 10 * 32 + offset.val < 512,
    plane88UnusedGenSectionProperty (Fin.mk (10 * 32 + offset.val) hlt) := by
  simp only [plane88UnusedGenSectionProperty, plane88UnusedGenConfig, plane88UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
