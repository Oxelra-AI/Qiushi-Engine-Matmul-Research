import QiushiPlane477GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane477GenDeadBlock12 : forall offset : Fin 32,
    forall hlt : 12 * 32 + offset.val < 512,
    plane477GenDeadProperty (Fin.mk (12 * 32 + offset.val) hlt) := by
  simp only [plane477GenDeadProperty, plane477GenConfig, plane477GenOccSys]
  decide +kernel
end QiushiMatmul
