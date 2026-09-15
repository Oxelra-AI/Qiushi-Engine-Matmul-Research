import QiushiPlane487GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane487GenSourceBlock16 : forall offset : Fin 32,
    forall hlt : 16 * 32 + offset.val < 668,
    plane487GenSourceProperty (Fin.mk (16 * 32 + offset.val) hlt) := by
  simp only [plane487GenSourceProperty, plane487GenConfig, plane487GenOccSys]
  decide +kernel
end QiushiMatmul
