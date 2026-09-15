import QiushiGlobalOrbitUnused305CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane305UnusedGenDeadBlock1 : forall offset : Fin 128,
    forall hlt : 1 * 128 + offset.val < 512,
    plane305UnusedGenDeadProperty (Fin.mk (1 * 128 + offset.val) hlt) := by
  simp only [plane305UnusedGenDeadProperty, plane305UnusedGenConfig, plane305UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
