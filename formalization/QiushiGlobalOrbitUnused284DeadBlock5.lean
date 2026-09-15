import QiushiGlobalOrbitUnused284CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane284UnusedGenDeadBlock5 : forall offset : Fin 32,
    forall hlt : 5 * 32 + offset.val < 512,
    plane284UnusedGenDeadProperty (Fin.mk (5 * 32 + offset.val) hlt) := by
  simp only [plane284UnusedGenDeadProperty, plane284UnusedGenConfig, plane284UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
