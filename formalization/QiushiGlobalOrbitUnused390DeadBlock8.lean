import QiushiGlobalOrbitUnused390CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane390UnusedGenDeadBlock8 : forall offset : Fin 32,
    forall hlt : 8 * 32 + offset.val < 512,
    plane390UnusedGenDeadProperty (Fin.mk (8 * 32 + offset.val) hlt) := by
  simp only [plane390UnusedGenDeadProperty, plane390UnusedGenConfig, plane390UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
