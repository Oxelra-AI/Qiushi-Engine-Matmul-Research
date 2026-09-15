import QiushiGlobalOrbitUnused404CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane404UnusedGenDeadSourceBlock0 : forall offset : Fin 128,
    forall hlt : 0 * 128 + offset.val < 17,
    plane404UnusedGenDeadSourceProperty (Fin.mk (0 * 128 + offset.val) hlt) := by
  simp only [plane404UnusedGenDeadSourceProperty, plane404UnusedGenConfig, plane404UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
