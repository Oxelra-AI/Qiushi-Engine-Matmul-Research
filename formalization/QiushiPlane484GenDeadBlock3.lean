import QiushiPlane484GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane484GenDeadBlock3 : forall offset : Fin 32,
    forall hlt : 3 * 32 + offset.val < 512,
    plane484GenDeadProperty (Fin.mk (3 * 32 + offset.val) hlt) := by
  simp only [plane484GenDeadProperty, plane484GenConfig, plane484GenOccSys]
  decide +kernel
end QiushiMatmul
