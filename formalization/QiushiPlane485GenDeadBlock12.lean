import QiushiPlane485GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane485GenDeadBlock12 : forall offset : Fin 32,
    forall hlt : 12 * 32 + offset.val < 512,
    plane485GenDeadProperty (Fin.mk (12 * 32 + offset.val) hlt) := by
  simp only [plane485GenDeadProperty, plane485GenConfig, plane485GenOccSys]
  decide +kernel
end QiushiMatmul
