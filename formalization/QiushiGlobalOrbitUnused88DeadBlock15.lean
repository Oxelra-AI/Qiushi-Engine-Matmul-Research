import QiushiGlobalOrbitUnused88CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane88UnusedGenDeadBlock15 : forall offset : Fin 32,
    forall hlt : 15 * 32 + offset.val < 512,
    plane88UnusedGenDeadProperty (Fin.mk (15 * 32 + offset.val) hlt) := by
  simp only [plane88UnusedGenDeadProperty, plane88UnusedGenConfig, plane88UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
