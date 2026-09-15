import QiushiGlobalOrbitUnused408CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane408UnusedGenDeadBlock3 : forall offset : Fin 128,
    forall hlt : 3 * 128 + offset.val < 512,
    plane408UnusedGenDeadProperty (Fin.mk (3 * 128 + offset.val) hlt) := by
  simp only [plane408UnusedGenDeadProperty, plane408UnusedGenConfig, plane408UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
