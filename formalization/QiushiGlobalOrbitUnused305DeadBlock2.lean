import QiushiGlobalOrbitUnused305CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane305UnusedGenDeadBlock2 : forall offset : Fin 128,
    forall hlt : 2 * 128 + offset.val < 512,
    plane305UnusedGenDeadProperty (Fin.mk (2 * 128 + offset.val) hlt) := by
  simp only [plane305UnusedGenDeadProperty, plane305UnusedGenConfig, plane305UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
