import QiushiPlane490GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane490GenSourceBlock12 : forall offset : Fin 32,
    forall hlt : 12 * 32 + offset.val < 713,
    plane490GenSourceProperty (Fin.mk (12 * 32 + offset.val) hlt) := by
  simp only [plane490GenSourceProperty, plane490GenConfig, plane490GenOccSys]
  decide +kernel
end QiushiMatmul
