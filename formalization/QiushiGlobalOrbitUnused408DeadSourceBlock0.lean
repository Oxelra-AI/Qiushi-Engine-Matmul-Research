import QiushiGlobalOrbitUnused408CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane408UnusedGenDeadSourceBlock0 : forall offset : Fin 128,
    forall hlt : 0 * 128 + offset.val < 13,
    plane408UnusedGenDeadSourceProperty (Fin.mk (0 * 128 + offset.val) hlt) := by
  simp only [plane408UnusedGenDeadSourceProperty, plane408UnusedGenConfig, plane408UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
