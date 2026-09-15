import QiushiGlobalOrbitUnused378CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane378UnusedGenDeadBlock3 : forall offset : Fin 128,
    forall hlt : 3 * 128 + offset.val < 512,
    plane378UnusedGenDeadProperty (Fin.mk (3 * 128 + offset.val) hlt) := by
  simp only [plane378UnusedGenDeadProperty, plane378UnusedGenConfig, plane378UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
