import QiushiPlane472GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane472GenDeadBlock3 : forall offset : Fin 32,
    forall hlt : 3 * 32 + offset.val < 512,
    plane472GenDeadProperty (Fin.mk (3 * 32 + offset.val) hlt) := by
  simp only [plane472GenDeadProperty, plane472GenConfig, plane472GenOccSys]
  decide +kernel
end QiushiMatmul
