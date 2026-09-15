import QiushiPlane458GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane458GenDeadBlock8 : forall offset : Fin 32,
    forall hlt : 8 * 32 + offset.val < 512,
    plane458GenDeadProperty (Fin.mk (8 * 32 + offset.val) hlt) := by
  simp only [plane458GenDeadProperty, plane458GenConfig, plane458GenOccSys]
  decide +kernel
end QiushiMatmul
