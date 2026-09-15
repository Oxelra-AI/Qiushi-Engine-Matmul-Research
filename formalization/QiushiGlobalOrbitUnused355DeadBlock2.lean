import QiushiGlobalOrbitUnused355CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane355UnusedGenDeadBlock2 : forall offset : Fin 128,
    forall hlt : 2 * 128 + offset.val < 512,
    plane355UnusedGenDeadProperty (Fin.mk (2 * 128 + offset.val) hlt) := by
  simp only [plane355UnusedGenDeadProperty, plane355UnusedGenConfig, plane355UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
