import QiushiGlobalOrbitUnused203CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane203UnusedGenDeadBlock12 : forall offset : Fin 32,
    forall hlt : 12 * 32 + offset.val < 512,
    plane203UnusedGenDeadProperty (Fin.mk (12 * 32 + offset.val) hlt) := by
  simp only [plane203UnusedGenDeadProperty, plane203UnusedGenConfig, plane203UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
