import QiushiPlane472GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane472GenDeadBlock6 : forall offset : Fin 32,
    forall hlt : 6 * 32 + offset.val < 512,
    plane472GenDeadProperty (Fin.mk (6 * 32 + offset.val) hlt) := by
  simp only [plane472GenDeadProperty, plane472GenConfig, plane472GenOccSys]
  decide +kernel
end QiushiMatmul
