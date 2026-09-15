import QiushiPlane459GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane459GenSourceBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 42,
    plane459GenSourceProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane459GenSourceProperty, plane459GenConfig, plane459GenOccSys]
  decide +kernel
end QiushiMatmul
