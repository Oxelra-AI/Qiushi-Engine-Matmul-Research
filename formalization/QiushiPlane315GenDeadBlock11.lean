import QiushiPlane315GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane315GenDeadBlock11 : forall offset : Fin 32,
    forall hlt : 11 * 32 + offset.val < 512,
    plane315GenDeadProperty (Fin.mk (11 * 32 + offset.val) hlt) := by
  simp only [plane315GenDeadProperty, plane315GenConfig, plane315GenOccSys]
  decide +kernel
end QiushiMatmul
