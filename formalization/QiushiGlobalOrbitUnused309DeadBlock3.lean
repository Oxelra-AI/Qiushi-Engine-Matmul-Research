import QiushiGlobalOrbitUnused309CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane309UnusedGenDeadBlock3 : forall offset : Fin 32,
    forall hlt : 3 * 32 + offset.val < 512,
    plane309UnusedGenDeadProperty (Fin.mk (3 * 32 + offset.val) hlt) := by
  simp only [plane309UnusedGenDeadProperty, plane309UnusedGenConfig, plane309UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
