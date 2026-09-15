import QiushiGlobalOrbitUnused249CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane249UnusedGenDeadBlock2 : forall offset : Fin 32,
    forall hlt : 2 * 32 + offset.val < 512,
    plane249UnusedGenDeadProperty (Fin.mk (2 * 32 + offset.val) hlt) := by
  simp only [plane249UnusedGenDeadProperty, plane249UnusedGenConfig, plane249UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
